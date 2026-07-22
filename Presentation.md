
## Content

- Our Topic
  - Overview over topics / classes
    - class diagram with all structures
- What we did & what we learned
  - (Advanced) Lean features
    - Typeclasses: Journey to how to best represent mathematical structures
        - Syntax is strongly coupled with typeclasses
    - Quotients
    - Macros (two kinds)
    - (Heterogenous equality??)
    - Coersions
    - Custom notation
    - 
- Our optinion on lean / Conclusion
    - what we liked
    - Common hickups / What we missed


## JZ
- Type class hierarchy
  - how to model mathematical structures: multiple approaches with problems
    - how to place arguments?
      - arguments (outputParam), member, inheritance
        - parameter for operation: closest to math, group for different operations
          - also possible because of multiple insantiation
        - member: everything is possible, especially for/with dependent options
          - same type group multiple times still possible though, yet automatic typeclass 
          - resolution not detectable, finecky with priority rules etc 
        - ineritance: use symbol in definition, cleanest
    - then it's not generic over syntax ;( ?
      - explicit functions are hard to use
        - there is also no inline backtick
      - just don't like in mathlib
  - how to compose typeclasses?
    - Field is two groups?
    - not possible to extend the same twice
  - Using Structure as type => x: G: CoeSort (also coe fun)
- how to deal with lots of unfolding for typeclasses
  - explicit theorems to do all at once
  - macro tactic
    - also as default argument in type class
    - practical as default values in typeclasses (which get only evaluated and checked on instanciation)
  - (unrelated?) it is hard to see that type classes are note the same (But look the same)
    - some kind of tree diff would be really helpful here!


Still open
- inverse definition
- simp rules
  - how to make them complete, sensable, all of them (e.g. also for minus etc.)
- actual theorems we did for typeclasses


Type class hierarchy story line
- Class resolution
  - output Param
- cumbersome to use, hard to read
  - inline syntax hack (§G.op§)
- still not that nice 
  - custom notation 
    - not usable in def, but ok
- For Field: use appropriate syntax (do not overload old ones)
  - use Add typeclass etc
- needs to be already used in definition, not only afterwards, (is syntactically different)
  - already derive initally
