`println("hello")` inferred as: `println(kotlin.String)`

Candidates set:
- `println(kotlin.Int)` from kotlin.io.ConsoleKt (1)
- [...] from kotlin.io.ConsoleKt
- `println(char[])` from kotlin.io.ConsoleKt (2)
- `println(kotlin.Any)` from kotlin.io.ConsoleKt (i.e.: `private static final void println(java.lang.Object)` in bytecode) (3)
- [...] (irrelevant) from other files


`java.lang.String`: `public final class java.lang.String implements java.io.Serializable, java.lang.Comparable<java.lang.String>, java.lang.CharSequence, java.lang.constant.Constable, java.lang.constant.ConstantDesc`


**Target:** java.lang.String -> java.lang.Object -> resolve to `println(Any)` (3)

---
`var a: Int = 3; println(a)` inferred as: `println(kotlin.Int)`

Candidates set:
- `println(kotlin.Int)` from kotlin.io.ConsoleKt (1)
- [...] from kotlin.io.ConsoleKt
- `println(char[])` from kotlin.io.ConsoleKt (2)
- `println(kotlin.Any)` from kotlin.io.ConsoleKt (i.e.: `private static final void println(java.lang.Object)` in bytecode) (3)
- [...] (irrelevant) from other files


**Target**: Resolve to (1)


## Determine function applicability

```
bool is_candidate_applicable() {

  for candidate in candidates {
    for arg of type Ti in arguments at call site {
      Uj is the corresponding function parameter type as declared (i!=j due to named parameters, but for us for now, i==j)

      Add constraint: Ti subtype of Uj
    }
    Add remaining constraints from declaration site (e.g.: remaining arguments?)

    return are_constraints_sound()
  }
}
```

Example: `var a: Int = 3; println(a)`, inferred as Int (integer literals have special rules that's why the example is not `println(3)`).

- Candidate `println(kotlin.Int)`: 
  + Add constraint: Int subtype of Int
  + Check constraints: ok.
- Candidate: `println(kotlin.Any)`:
  + Add constraint: Int subtype of Any
  + Check constraints: ok.
- Candidate: `println(kotlin.Double)`:
  + Add constraint: Widen(Int) (i.e.: `kotlin.Int & kotlin.Short & kotlin.Byte & kotlin.Long`) subtype of Widen(Double) (i.e.: `kotlin.Double`) (would we even call Widen on a non integer type?)
  + Check constraints: no! Because: `kotlin.Int & kotlin.Short & kotlin.Byte & kotlin.Long` is not a subtype of `kotlin.Double`.
- Candidate: `println(kotlin.Short)`:
  + Add constraint: Widen(Int) (i.e.: `kotlin.Int & kotlin.Short & kotlin.Byte & kotlin.Long`) subtype of Widen(Short) (i.e.: `kotlin.Short & kotlin.Byte`) 
  + Check constraints: no! Because: `kotlin.Int & kotlin.Short & kotlin.Byte & kotlin.Long` is NOT a subtype of `kotlin.Short & kotlin.Byte`. 



NOTE: `A & B` <=> `GLB(A, B)`, and: `A & B & C` <=> `A & (B & C)` <=> `GLB(A, GLB(B, C))`

NOTE: if `A subtype of B`: `GLB(A, B) = A`

NOTE: `A & B` subtype of `A` e.g.: `kotlin.Short & kotlin.Byte` subtype of `kotlin.Short`.

NOTE: `A & B` subtype of `B` e.g.: `kotlin.Short & kotlin.Byte` subtype of `kotlin.Byte`.

NOTE: `A subtype of C and B subtype of D` => `A & B subtype of C & D`


Corollaries:
- `kotlin.Int & ...` subtype of `kotlin.Int`
- Checking the constraint of `T subtype of U` where T and U are both integer types is trivial: it becomes a `is in set` check.
  + E.g.: `kotlin.Long` subtype of `kotlin.Int` ? 
    - `Widen(kotlin.Long)` = `kotlin.Long`
    - `Widen(kotlin.Int)` = `kotlin.Int & kotlin.Short & kotlin.Byte & kotlin.Long`
    - Hence: `kotlin.Long` is a subtype of `kotlin.Int` because: `kotlin.Int & ... & kotlin.Long` is a subtype of `kotlin.Int` and is a subtype of `kotlin.Long`.
    - Also: `kotlin.Int` is a subtype of `kotlin.Long`
  + But: `kotlin.Long` subtype of `kotlin.Short`?
    - `Widen(kotlin.Long)` = `kotlin.Long`
    - `Widen(kotlin.Short)` = `kotlin.Short & kotlin.Byte`
    - Hence: `kotlin.Long` is NOT a subtype of `kotlin.Short` because: `kotlin.Long` is not in `[kotlin.Short, kotlin.Byte]`
    - Hence: `kotlin.Short` is NOT a subtype of `kotlin.Long` because: `kotlin.Short` is not in `[kotlin.Long]` and `kotlin.Byte` is not in `[kotlin.Long]`



## Most Specific Candidate algorithm:

```
for K1, K2 unique pair of candidates from the candidates set {
  X1 is the declaration-site parameter type of K1 number 1
  Y1 is the declaration-site parameter type of K2 number 1

  if (is_integer(X1) and is_integer(Y1) {
    Add constraint: Widen(X1) subtype of Widen(Y1)
  } else {
    Add constraint: X1 subtype of Y1
  }
}
```

Example: `println("hello")`

Applicable functions:
- `println(Any)`
- 

