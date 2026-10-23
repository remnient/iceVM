# iceVM

iceVM implements a register VM + Rocq compiler and checked bytecode optimisations

the VM itself is small with 16 64-bit registers, byte-addressable memory and an explicit call stack while the Rocq semantics makes decoding failures and  runtime traps part of the execution model

 the compiler proof accounts for recursion, faults and the extra instructions introduced during compilation +  optimisation candidates go through a checker that proves they preserve results along with traps and divergence
 
 the C runtime also has VST proofs, though these establish partial correctness under allocator contracts and still leave extraction, the host compiler and I/O trusted