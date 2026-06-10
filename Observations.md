# Things we noticed or learned during this project

- Type classes with operation as parameter can be cumbersome to use if this operation cannot be interred automatically for some members and thus needs to be specified. This can be improved by using explicitly naming `[g: Group G op]` and the referring to `g.neutral`, for example. 
- Infix operators are difficult for generic type classes
- Deriving from the same type class multiple times is not possible, can be solved by having structure member that asserts its implementation
- Subtyping helps for fields?
- Add and similar are not just syntactic sugar. Lean automatically resolves their definitions in less places than expected. One reliable way to do that is to explicitly define the type with `have x: ...`, or using `unfold Add.add` for one direction.
- Default values in structures cannot be assumed to not be overwritten, even if they are not. Thus, if you want to use them for syntactic sugar, it often helps to also provide a theorem that they have their expected value (with a default proof.)
- Type classes and theirs search algorithm are very sophisticated. Knowing the right options to set (i.e. outputParam) can make the compile behave as wanted.
- `CoeSort` is nice
- Implicit arguments are dangerous, if they sometimes are not implicit (but a global "variable)
- Inheritance and type classes for each operation (inv etc.) allows to use symbols directly in definitions and makes everything clean
- Default values in type classes are only compile checked at instantiation.
- It is best to use the actual notation (i.e. +, *) on theorems directly to apply them. Thus, using them in the definition of fields is desired. This may require defining them stepwise (first the operation, then in another class the axioms). It now also makes sense why the mathlib has seperate classes for and and mul groups, as they are tightly tied to notation. It may still be possible to have multiple different groups on the same set (if that is even mathematically possible) due to multiple instantiation of the same class. We may even want to just use + syntax i groups, as that is what is wanted for fields and vector spaces, and having a different underlying syntax makes for the additive group makes the field awkward to handle.
- In lean, x / 0:= 0. We wanted to do this more true to mathematical convention and have the inverse not defined on zero. We will see how cumbersome this will be.
- Type classes can be annoying, especially when they look the same (two times 0), but are not quite, or require internal unfolding to prove this. In general can be annoying.