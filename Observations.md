# Things we noticed or learned during this project

- Type classes with operation as parameter can be cumbersome to use if this operation cannot be interred automatically for some members and thus needs to be specified. This can be improved by using explicitly naming `[g: Group G op]` and the referring to `g.neutral`, for example. 