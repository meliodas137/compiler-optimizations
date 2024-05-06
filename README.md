# Compiler Optimizations
A data flow analysis based compiler optimizations. Building an intermediate control flow graph and applying optimizations techniques before generating the final MIPS assembly code.

If you run `make` it produces a binary called ./optimize. Running

 ./optimize [name of cish file]

calls the Cish 2 block converter, then runs the following optimizations in the order:
<ul>
<li>Common Subexpression Elimination
<li>Copy Propagation
<li>Constant Propagation
<li>Dead Code Elimination
</ul>

Besides, there are additional test files in the folder named "test".
