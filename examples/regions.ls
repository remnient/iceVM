def main():
    base = mark()
    p = alloc(8)
    i = 0
    total = 0
    while i < 10:
        total = total + i
        i = i + 1
    store(p, total)
    result = load(p)
    reset(base)
    return result
