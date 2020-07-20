# LLVM-pass-to-implement-support-for-nested-functions-in-C

IISc Course Project: Compiler Design


C syntax does not support nested functions natively, my work emulates nested function definition using labeled blocks where the label will beconsidered as the name of the nested function. Given nested functions (as labeled blocks), my implementation does AST transformation and outputs a valid AST and valid C code that has the behaviour of nested functions.


All the support for recursion and data types are preserved.
