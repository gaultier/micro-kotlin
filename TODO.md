[x] Add JVM function types
[x] Generate type descriptors as strings
[.] Read class files and keep a map of function name to signature (copy descriptor strings, skip building them?)
[x] Semantic opcode generation functions
[.] Keep track of the stack & locals
[ ] Call functions
[ ] Define functions
[ ] Generate stack map tables
[ ] Use latest jvm version
[x] Makefile/build.sh
[x] Log memory used in arena
[ ] Write non-trivial program with the API (opcode generation functions)
[x] Compute class file name

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
        4. Put it in a map/array
    2. For each field:
        1. Skip if not public (TODO: skip if not accessible e.g. not in the same package, etc)
        2. Record the name and descriptor
        3. Sanity checks
        4. Put it in a map/array

Open questions:

- Do we want to record attributes of each field/method? It could allow e.g. inlining of the code.


## Points where I'm not sure  about in the code

- Should the different arrays be macros
- Should the array len/cap be u16 when that's the class file format
- Tagged unions vs a big struct with flags?
