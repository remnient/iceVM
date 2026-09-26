import ast
BIN = {ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.FloorDiv: 'div',
       ast.BitAnd: 'and', ast.BitOr: 'or', ast.BitXor: 'xor',
       ast.LShift: 'shl', ast.RShift: 'shr'}


def serialise_source(text):
    tree = ast.parse(text)
    functions = {}
    for f in tree.body:
        if not isinstance(f, ast.FunctionDef) or f.decorator_list or f.returns or getattr(f, 'type_params', []):
            raise ValueError('a program contains only undecorated function definitions')
        if f.name in functions or f.name in ('load', 'alloc', 'store', 'mark', 'reset'):
            raise ValueError(f'duplicate or reserved function {f.name}')
        if len(f.args.args) != (0 if f.name == 'main' else 1):
            raise ValueError('main takes no arguments; other functions take one argument')
        if f.args.posonlyargs or f.args.kwonlyargs or f.args.vararg or f.args.kwarg or f.args.defaults:
            raise ValueError('unsupported function signature')
        functions[f.name] = f
    if 'main' not in functions:
        raise ValueError('missing main function')
    names = ['main'] + [n for n in functions if n != 'main']
    ids = {name: i for i, name in enumerate(names)}
    out = []
    for name in names:
        f = functions[name]
        locals_ = {}
        if f.args.args:
            locals_[f.args.args[0].arg] = 0
        for node in ast.walk(f):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Name) and target.id not in locals_:
                        locals_[target.id] = len(locals_)

        if len(locals_) > 8:
            raise ValueError('at most eight local variables per function')

        def expr(e):
            if isinstance(e, ast.Constant) and isinstance(e.value, (int, bool)):
                return f'(lit {int(e.value) & ((1 << 64) - 1)})'
            if isinstance(e, ast.Name):
                if e.id not in locals_:
                    raise ValueError(f'unknown local {e.id}')
                return f'(var {locals_[e.id]})'
            if isinstance(e, ast.BinOp) and type(e.op) in BIN:
                return f'(bin {BIN[type(e.op)]} {expr(e.left)} {expr(e.right)})'
            if isinstance(e, ast.Compare) and len(e.ops) == 1:
                a, b, op = expr(e.left), expr(e.comparators[0]), type(e.ops[0])
                if type(e.ops[0]) not in (ast.Eq, ast.NotEq, ast.Lt, ast.LtE, ast.Gt, ast.GtE):
                    raise ValueError('unsupported comparison')
                symbol = {ast.Eq: 'eq', ast.NotEq: 'ne', ast.Lt: 'lt', ast.LtE: 'le',
                          ast.Gt: 'gt', ast.GtE: 'ge'}[op]
                return f'(cmp {symbol} {a} {b})'
            if isinstance(e, ast.UnaryOp) and isinstance(e.op, (ast.Not, ast.USub, ast.Invert)):
                if isinstance(e.op, ast.Not):
                    return f'(bin eq {expr(e.operand)} (lit 0))'
                if isinstance(e.op, ast.USub):
                    return f'(bin sub (lit 0) {expr(e.operand)})'
                return f'(bin xor (lit 18446744073709551615) {expr(e.operand)})'
            if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and not e.keywords:
                name = e.func.id
                if name == 'mark' and not e.args:
                    return '(mark)'
                if name in ('load', 'alloc') and len(e.args) == 1:
                    return f'({name} {expr(e.args[0])})'
                if name in ids and name != 'main' and len(e.args) == 1:
                    return f'(call {ids[name]} {expr(e.args[0])})'
            raise ValueError('invalid source expression')

        def stmt(s):
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
                return f'(set {locals_[s.targets[0].id]} {expr(s.value)})'
            if isinstance(s, ast.Return) and s.value is not None:
                return f'(return {expr(s.value)})'
            if isinstance(s, ast.If):
                return f'(if {expr(s.test)} {body(s.body)} {body(s.orelse)})'
            if isinstance(s, ast.While) and not s.orelse:
                return f'(while {expr(s.test)} {body(s.body)})'
            if isinstance(s, ast.Pass):
                return '(skip)'
            if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
                call = s.value
                if not isinstance(call.func, ast.Name) or call.keywords:
                    raise ValueError('invalid statement call')
                if call.func.id == 'store' and len(call.args) == 2:
                    return f'(store {expr(call.args[0])} {expr(call.args[1])})'
                if call.func.id == 'reset' and len(call.args) == 1:
                    return f'(reset {expr(call.args[0])})'
                return f'(discard {expr(call)})'
            raise ValueError('invalid source statement')

        def body(statements):
            result = '(skip)'
            for s in reversed(statements):
                result = f'(seq {stmt(s)} {result})'
            return result

        out.append(f'(seq {body(f.body)} (return (lit 0)))')
    return '(' + ' '.join(out) + ')'


def source_certificate(text):
    import io
    import tokenize

    def name(text):
        return '(' + ' '.join(str(ord(c)) for c in text) + ')'

    rows = []
    for line in text.splitlines():
        if '\t' in line[:len(line) - len(line.lstrip())]:
            raise ValueError('indentation uses spaces')
        indent = len(line) - len(line.lstrip(' '))
        tokens = [t.string for t in tokenize.generate_tokens(io.StringIO(line[indent:]).readline)
                  if t.type not in (tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT)]
        if tokens:
            rows.append((indent, tokens))

    binary = {'|': ('or', 3), '^': ('xor', 4), '&': ('and', 5),
              '<<': ('shl', 6), '>>': ('shr', 6), '+': ('add', 7), '-': ('sub', 7),
              '*': ('mul', 8), '//': ('div', 8)}
    comparisons = {'==': 'eq', '!=': 'ne', '<': 'lt', '<=': 'le', '>': 'gt', '>=': 'ge'}

    def expression(tokens):
        pos = 0

        def take(expected=None):
            nonlocal pos
            if pos >= len(tokens) or expected is not None and tokens[pos] != expected:
                raise ValueError('invalid expression')
            t = tokens[pos]
            pos += 1
            return t

        def parse(precedence):
            nonlocal pos
            t = take()
            if t in ('-', '~', 'not'):
                p = 1 if t == 'not' else 9
                if precedence > p:
                    raise ValueError('invalid unary precedence')
                u = {'-': 'neg', '~': 'invert', 'not': 'not'}[t]
                lhs = f'(unary {u} {parse(p)})'
            elif t == '(':
                lhs = f'(paren {parse(0)})'
                take(')')
            elif t in ('True', 'False'):
                lhs = f'(boolean {t.lower()})'
            elif t[0].isdigit():
                lhs = f'(literal {int(t, 0)})'
            elif t.isidentifier():
                if pos < len(tokens) and tokens[pos] == '(':
                    take('(')
                    if pos < len(tokens) and tokens[pos] == ')':
                        lhs = f'(call0 {name(t)})'
                    else:
                        lhs = f'(call1 {name(t)} {parse(0)})'
                    take(')')
                else:
                    lhs = f'(name {name(t)})'
            else:
                raise ValueError('invalid expression token')
            compared = False
            while pos < len(tokens):
                op = tokens[pos]
                if op in comparisons and precedence <= 2 and not compared:
                    pos += 1
                    lhs = f'(comparison {comparisons[op]} {lhs} {parse(3)})'
                    compared = True
                elif op in binary and binary[op][1] >= precedence:
                    pos += 1
                    symbol, p = binary[op]
                    lhs = f'(binary {symbol} {lhs} {parse(p + 1)})'
                else:
                    break
            return lhs

        result = parse(0)
        if pos != len(tokens):
            raise ValueError('trailing expression tokens')
        return result

    pos = 0

    def block(indent):
        nonlocal pos
        statements = []
        while pos < len(rows) and rows[pos][0] == indent:
            _, tokens = rows[pos]
            pos += 1
            if tokens == ['pass']:
                s = '(pass)'
            elif tokens[0] == 'return':
                s = f'(return {expression(tokens[1:])})'
            elif len(tokens) > 1 and tokens[1] == '=':
                s = f'(assign {name(tokens[0])} {expression(tokens[2:])})'
            elif tokens[0] in ('if', 'while') and tokens[-1] == ':':
                if pos >= len(rows) or rows[pos][0] <= indent:
                    raise ValueError('missing nested block')
                cond = expression(tokens[1:-1])
                yes = block(rows[pos][0])
                if tokens[0] == 'while':
                    s = f'(while {cond} {yes})'
                elif pos < len(rows) and rows[pos] == (indent, ['else', ':']):
                    pos += 1
                    if pos >= len(rows) or rows[pos][0] <= indent:
                        raise ValueError('missing else block')
                    s = f'(if {cond} {yes} {block(rows[pos][0])})'
                else:
                    s = f'(ifthen {cond} {yes})'
            elif tokens[0] == 'store' and tokens[1:2] == ['('] and tokens[-1] == ')':
                depth = 0
                comma = None
                for i, t in enumerate(tokens[2:-1], 2):
                    if t == '(':
                        depth += 1
                    elif t == ')':
                        depth -= 1
                    elif t == ',' and depth == 0:
                        comma = i
                        break
                if comma is None:
                    raise ValueError('store takes two arguments')
                s = f'(store {expression(tokens[2:comma])} {expression(tokens[comma + 1:-1])})'
            elif tokens[0] == 'reset' and tokens[1:2] == ['('] and tokens[-1] == ')':
                s = f'(reset {expression(tokens[2:-1])})'
            else:
                s = f'(discard {expression(tokens)})'
            statements.append(s)
        result = '(end)'
        for s in reversed(statements):
            result = f'(then {s} {result})'
        return result

    functions = []
    while pos < len(rows):
        indent, tokens = rows[pos]
        if indent != 0 or len(tokens) not in (5, 6) or tokens[0] != 'def' or tokens[2] != '(' or tokens[-2:] != [')', ':']:
            raise ValueError('invalid function header')
        parameter = '(none)' if len(tokens) == 5 else f'(some {name(tokens[3])})'
        pos += 1
        if pos >= len(rows) or rows[pos][0] == 0:
            raise ValueError('missing function body')
        functions.append(f'({name(tokens[1])} {parameter} {block(rows[pos][0])})')
    return '(' + ' '.join(functions) + ')'
