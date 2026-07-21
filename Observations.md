# Things we noticed or learned during this project

- Type classes with operation as parameter can be cumbersome to use if this operation cannot be interred automatically for some members and thus needs to be specified. This can be improved by using explicitly naming `[g: Group G op]` and the referring to `g.neutral`, for example. 
- Infix operators are difficult for generic type classes
- Deriving from the same type class multiple times is not possible, can be solved by having structure member that asserts its implementation
- Subtyping helps for fields?
- Add and similar are not just syntactic sugar. Lean automatically resolves their definitions in less places than expected. One reliable way to do that is to explicitly define the type with `have x: ...`, or using `unfold Add.add` for one direction.
- Default values in structures cannot be assumed to not be overwritten, even if they are not. Thus, if you want to use them for syntactic sugar, it often helps to also provide a theorem that they have their expected value (with a default proof.)
- Type classes and theirs search algorithm are very sophisticated. Knowing the right options to set (i.e. outputParam) can make the compiler behave as wanted.
- `CoeSort` is nice
- Implicit arguments are dangerous, if they sometimes are not implicit (but a global "variable")
- Inheritance and type classes for each operation (inv etc.) allows using symbols directly in definitions and makes everything clean
- Default values in type classes are only compile checked at instantiation.
- It is best to use the actual notation (i.e. +, *) on theorems directly to apply them. Thus, using them in the definition of fields is desired. This may require defining them stepwise (first the operation, then in another class the axioms). It now also makes sense why the mathlib has separate classes for and mul groups, as they are tightly tied to notation. It may still be possible to have multiple different groups on the same set (if that is even mathematically possible) due to multiple instantiation of the same class. We may even want to just use + syntax i groups, as that is what is wanted for fields and vector spaces, and having a different underlying syntax makes for the additive group makes the field awkward to handle.
- In lean, x / 0:= 0. We wanted to do this more true to mathematical convention and have the inverse not defined on zero. We will see how cumbersome this will be.
- Type classes can be annoying, especially when they look the same (two times 0), but are not quite, or require internal unfolding to prove this. In general can be annoying.
Custom tactics are really powerful here, allowing one to automate this process. In general, leans syntax is very extensible. This can be nicely combined with type class default values, which are only evaluated at instantiation time to provide default unfolding proofs.
- It's not that easy to do simp rules right that they are not annoying but actually make things more simple. This may require to build a "hull" of theorems, e.g. if x - y is simpler than x + -y, we also want distributivity for a * (x - y).
- Lean is not a very stable language: Just adding some simp rules can easily break many proofs. Fixing them afterward is not that easy if they are not easy to read. Further, just importing modules (i.e. parts of mathlib) can again break proofs (because it probably introduces its own simp rules). As a consequence, proofers should use almighty simp rules sparingly, and maybe use dsimp, (d)simp only if sufficient instead. Further, making things simp rules should be a conscious decision, as this creates implicit dependencies. 
- Lists can be tedious to work with. Mathlib may help here as there are further lemmas. In general, making things formal on sums is a bit tedious. In practice people hand wave a log of obvious facts here. Sums over lists are probably better than with an additional mapping function.
- 