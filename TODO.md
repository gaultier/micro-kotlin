**TODO now!:**

- [x] Add JVM function types
- [x] Generate type descriptors as strings
- [x] Read class files and keep a map of function name to signature (copy descriptor strings, skip building them?)
- [x] Semantic opcode generation functions
- [x] Keep track of the stack & locals => Might need to do that at a higher level e.g. while working on the AST/IR
- [x] Call functions generically (no builtin) from the same class file
- [x] Call functions generically (no builtin) from other class files
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
- [ ] Decode UCS-2 Strings in class files (in constant pool)
- [x] Function definition
- [ ] Field access
- [x] String literals
- [x] Grouping
- [ ] Explicit casts
- [x] Long
- [x] Refactor/rename stuff
- [x] Add asm operations that does the right thing based on the locals/stack types (e.g. add: iadd | fadd | ladd | dadd)
- [x] Byte
- [ ] Char
- [x] Short
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
- [x] Control flow: Return
- [x] Checks around return
- [x] Move types to the resolver
- [x] Recursion (mutual recursion?)
- [ ] Multiple files - what about ordering and type hole filling?
- [x] Read .class, .jar, files in classpath for stdlib and such - only keep required data, don't read everything in the class path for efficiency
- [x] Read .jmod files
- [x] Add class path CLI option
- [x] Scan known locations for jmod files
- [x] Convert jvm types to kotlin types when reading .class, .jar, .jmod
- [x] Use scratch arena when reading .class, .jar, .jmod files
- [x] Merge functions to read .jmod, .jar if possible
- [x] Avoid duplicating method resolution in the resolver and the lowerer (descriptor)
- [ ] Defend against integer overflows
- [ ] Hex/other number literals
- [ ] Constant pool deduplication
- [ ] Hashes/Hashtables in judicious places in the compiler (strings, types?)
- [x] Heap dump on Linux, tracking of call stack during allocations.
- [ ] Heap dump on other OSes
- [ ] Heap dump on Linux with function names (instead of addresses)
- [ ] Heap dump on other OSes with function names (instead of addresses)
- [ ] **Union/intersection of integer types for integer literals**
- [ ] Package name
- [ ] Default imports
- [ ] Imports
- [x] Log the file/line of the function that was resolved
- [x] Resolve free functions by building candidate sets
- [x] Trivial inline (no jumps, no exceptions, etc)
- [x] Remove builtin println
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
  * Redundant conditions e.g. Byte > 128
  * Redundant if-then-else branches e.g. `if (false) 1 else if (true) 2 else 3`
  * All paths return a value in a function
  * Switch (`when`): All cases are covered
  * Switch (`when`): No redundant cases
  * ...

**Later:**

- [ ] Read kotlin metadata in class files (protobuf)
- [ ] Full-fledged type inference
- [x] Do not hold on constant pool strings from .jmod/.class/.jar files that are not useful (e.g. used for CONSTANT_POOL_KIND_CLASS_INFO, etc) to reduce memory usage
- [ ] High level APIs for the driver
- [ ] Generate line tables
- [ ] Generate full debug information
- [ ] Generate exceptions table
- [ ] Out-of-order declarations
- [ ] Bit operators
- [ ] Interfaces
- [ ] Using generics (BIG!)
- [ ] Defining generics (BIG!)
- [ ] Nullability checks
- [ ] Output jar file with all the classes inside

**Probably much later (not necessary for a MVP):**

- [ ] Infix functions
- [ ] Kdoc in comments
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
- [ ] Async stuff (suspend, etc)
- [ ] Java <-> Kotlin interop e.g. @JvmName, etc
- [ ] Runtime reflection
- [ ] Maybe: multi thread the compiler
- [ ] Maybe: implement/vendor libzip
- [ ] Optimize size of `allocation_metadata_t`

### kotlin.Metadata annotation in class file

- `mv` and `bv` are versions which are not interesting.
- `k` or `kind` is an enum value. 1: Class, 2: File.
- `d1` contains protobuf encoded data: 
  - Length-prefixed `StringTableTypes`: list of records and list of local names.
    * `predefined_index` in a Record is an index in the list `PREDEDEFINED_STRINGS` inside the kotlin compiler, e.g. `8` is `kotlin.Int`.
  - Depending on `k`:
    * If `k` is 1: `Class`.
    * If `k` is 2: `Package`.
      + `Package` contains a list of functions. Each function has a `name` field which is an index into the `d2` array of strings (?) and a return type whose field `class_name` is an index in the string table types (?).
- `d2`: Array of strings e.g. function names.


### `println`

- Defined in `libraries/stdlib/jvm/src/kotlin/io/Console.kt` are public inline functions with the annotation `@kotlin.internal.InlineOnly`.
- Compiled to private static final functions (thanks to the annotation?) on the class `ConsoleKt` with the runtime invisible annotation: `kotlin.interal.InlineOnly`.
- Thus cannot be used from Java as-is e.g. `kotlin.io.ConsoleKt.println(3);`.
- Can be used from Kotlin with the compiler copying ('inlining') the code when calling `kotlin.io.println(3)`. Thus there is no `ConsoleKt` class for the kotlinc compiler and `kotlin.io.ConsoleKt.println(3)` does not work.
- The compiler has a special case for `@InlineOnly` annotated functions, which are private in the bytecode but are considered public in kotlin code.




## Open questions

## Non-goals

- Class file size
- Optimizing generated code (for now, although it could be fun and there are lots of hanging fruits, e.g. constant propagation and Control Flow Graph (CFG)).
- Smartness
- Non JVM backends

## Goals

Primary target audience: developers with medium to large projects that are slow to compile.
Secondary target audience: developers using Kotlin but not Intellij who need good CLI tooling (later: formatting, LSP).

- Fast compile times (ideally < 1s for small to medium projects, < 10s for large projects). Target: 1M LOC/s.
- Fast import times (of bytecode). Target: 1G/s (with SSD).
- Generated code speed and size are within 2-10x of the code generated by the official compiler.
- Understable error messages, possibly great ones
- Small executable size for efficient CI downloading
- No dependencies. Possible exception: libzip to read jar files, but linked statically.
- Major platforms supported (including Windows :| )
- 'Dumb' codebase


