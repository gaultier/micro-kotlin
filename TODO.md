[x] Add JVM function types
[x] Generate type descriptors as strings
[x] Read class files and keep a map of function name to signature (copy descriptor strings, skip building them?)
[x] Semantic opcode generation functions
[.] Keep track of the stack & locals => Might need to do that at a higher level e.g. while working on the AST/IR
[ ] Call functions generically (no builtin) from the same class file
[ ] Call functions generically (no builtin) from other class files
[x] Define functions
[ ] Generate stack map tables
[ ] Use latest jvm version
[x] Makefile/build.sh
[x] Log memory used in arena
[x] Write non-trivial program with the API (opcode generation functions)
[x] Compute class file name
[ ] Naive register (e.g. locals) allocation
[ ] Type checking, no inference
[ ] Field access
[ ] Control flow

Sugar (nice to have):

[ ] Generate line tables
[ ] Generate full debug information
[ ] Generate exceptions table
[ ] Generate multi-threading stuff (volatile, synchronized, etc)

## Approach for reading external class files to know what fields/methods are available

1. For each class file in the class path:
    1. Parse the whole class file
    2. For each method:
        1. Skip if not public (TODO: skip if not accessible e.g. not in the same package, etc)
        2. Record the name and descriptor
        3. Sanity checks
        4. ~Put it in a map/array~
    2. For each field:
        1. Skip if not public (TODO: skip if not accessible e.g. not in the same package, etc)
        2. Record the name and descriptor
        3. Sanity checks
        4. ~Put it in a map/array~

Open questions:

- Do we want to record attributes of each field/method? It could allow e.g. inlining of the code. => Currently yes.
- How to implement generics
- Method resolution (complex)
- Do we want to implement both code for values and for references, or just for references a la Kotlin (but will it work with Java interop?) => Turns out Kotlin uses Java unboxed types for non-nullable cases.
- Lazily scan classpath as needed?


## Points where I'm not sure  about in the code

- Should the different arrays be macros => Currently, no.
- Should the array len/cap be u16 when that's the class file format
- Tagged unions vs a big struct with flags? => Memory usage issue with big structs for 30k+ class files.

## Non-goals

- Class file size
- Optimizing generated code
