import LinearAlgebraInLean.Util

syntax  "vector_space_refold" (" [" Lean.Parser.Tactic.simpLemma,*,? "]")? : tactic
macro_rules
  | `(tactic|vector_space_refold [$lma,*]) => `(tactic|
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, SMul.smul, OfNat.ofNat, Neg.neg, Zero.zero, $lma, *];
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat])
  | `(tactic|vector_space_refold ) => `(tactic| vector_space_refold [])


-- todo refold tactic
