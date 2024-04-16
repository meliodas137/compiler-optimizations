# Compiler Optimizations
A data flow analysis based compiler optimizations. Building an intermediate control flow graph and applying optimizations techniques before generating the final MIPS assembly code.

If you run `make` it produces a binary called ./optimize. Running

 ./optimize [name of cish file]

calls the Cish 2 block converter, then runs your interference graph generator,
and then tries to print the CFG blocks and the interference.
