**TODO now:**

- [x] Add JVM function types
- [x] Generate type descriptors as strings
- [x] Read class files and keep a map of function name to signature (copy descriptor strings, skip building them?)
- [x] Semantic opcode generation functions
- [x] Keep track of the stack & locals => Might need to do that at a higher level e.g. while working on the AST/IR
- [ ] Call functions generically (no builtin) from the same class file
- [ ] Call functions generically (no builtin) from other class files
- [x] Define functions
- [x] Generate stack map tables
- [x] Use latest jvm version
- [x] Makefile/build.sh
- [x] Log memory used in arena
- [x] Write non-trivial program with the API (opcode generation functions)
- [x] Compute class file name
- [x] Naive register (e.g. locals) allocation
- [x] Type checking, no inference
- [x] Local variables
- [ ] Comments
- [x] Local variable mutation
- [ ] Function definition
- [ ] [DOING] Field access
- [x] String literals
- [x] Grouping
- [ ] Casts
- [x] Long
- [ ] Refactor/rename stuff
- [x] Add asm operations that does the right thing based on the locals/stack types (e.g. add: iadd | fadd | ladd | dadd)
- [ ] Byte, Char, Short
- [ ] Double, Float
- [x] Control flow: If
- [x] Logical operator !
- [x] Comparison operators <,<=,>,>=,==,!=
- [x] Logical operators (and, or)
- [x] Control flow: While
- [ ] Control flow: Continue
- [ ] Control flow: Break
- [ ] Control flow: For (?)
- [ ] Control flow: When
- [ ] Control flow: Do-while
- [ ] Recursion (mutual recursion?)
- [ ] Multiple files - what about ordering and type hole filling?
- [ ] Packages
- [x] Read .class, .jar, files in classpath for stdlib and such - only keep required data, don't read everything in the class path for efficiency
- [x] Read .jmod files
- [ ] Defend against integer overflows
- [ ] Hex/other number literals
- [ ] Constant pool deduplication
- [ ] Hashes/Hashtables in judicious places in the compiler
- [ ] Class definition (BIG!)
  * Fields
  * Primary constructor
  * Secondary constructor
  * Methods
  * Static methods
  * Static fields
- [ ] Basic static analysis
  * Unused variables
  * Unreachable code (might require SSA/CFG?)
  * Mutable variables read from but never written to
  * Endless recursion
  * ...

**Later:**

- [ ] High level APIs for the driver
- [ ] Generate line tables
- [ ] Generate full debug information
- [ ] Generate exceptions table
- [ ] Out-of-order declarations
- [ ] Bit operators
- [ ] Interfaces
- [ ] Using generics (BIG!)
- [ ] Defining generics (BIG!)
- [ ] Casts
- [ ] Nullability checks

**Probably much later (not necessary for a MVP):**

- [ ] Infix functions
- [ ] Type flow (e.g. `if (x is String) x + "foo"`)
- [ ] Unicode identifiers
- [ ] Function names with spaces and backticks
- [ ] Ranges
- [ ] Vararg
- [ ] Tailrec
- [ ] Operator overloading
- [ ] Data class
- [ ] Raw (multiline) strings
- [ ] Nested (interpolation) strings 
- [ ] Property delegate
- [ ] Lazy/lateinit
- [ ] Multi-threading stuff (volatile, synchronized, etc)
- [ ] Annotation
- [ ] Complicated OOP stuff (companion objects, singleton, extension methods, etc)
- [ ] Inline
- [ ] Async stuff (suspend, etc)

## Naive approach for reading external class files to know what fields/methods are available

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

## Open questions

- ~~Do we want to record attributes of each field/method? It could allow e.g. inlining of the code.~~ Yes.
- How to implement generics
- Method resolution (complex)
- Type inference (complex)
- ~~Do we want to implement both code for values and for references, or just for references a la Kotlin (but will it work with Java interop?)~~ => Turns out Kotlin uses Java unboxed types for non-nullable cases.
- Lazily scan classpath as needed?


## Points where I'm not sure about in the code

- ~~Should the different arrays be macros~~ Yes.
- Should the array len/cap be u16 when that's the class file format
- Tagged unions vs a big struct with flags? => Memory usage issue with big structs for 30k+ class files.

## Non-goals

- Class file size
- Optimizing generated code (for now, although it could be fun and there are lots of hanging fruits, e.g. constant propagation and Control Flow Graph (CFG)).
- Smartness
- Non JVM backends

## Goals

Primary target audience: developers with medium to large projects that are slow to compile.
Secondary target audience: developers using Kotlin but not Intellij who need good CLI tooling (later: formatting, LSP).

- Fast compile times (ideally < 1s for small to medium projects, < 10s for large projects). Target: 1M LOC/s.
- Generated code speed and size are within 2-10x of the code generated by the official compiler.
- Understable error messages, possibly great ones
- Small executable size for efficient CI downloading
- No dependencies. Possible exception: libzip to read jar files, but linked statically.
- Major platforms supported (including Windows :| )
- 'Dumb' codebase
