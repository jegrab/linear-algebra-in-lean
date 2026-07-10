import LinearAlgebraInLean.Util
import Lean
open Lean Elab Tactic

syntax  "vector_space_refold" (" [" Lean.Parser.Tactic.simpLemma,*,? "]")? : tactic
macro_rules
  | `(tactic|vector_space_refold [$lma,*]) => `(tactic|
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, SMul.smul, OfNat.ofNat, Neg.neg, Zero.zero, $lma,*];
      try simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat])
  | `(tactic|vector_space_refold ) => `(tactic| vector_space_refold [])


-- todo refold tactic

def unfoldForall (e: Expr) : TacticM (List Name) := do
  match e with
  | Expr.forallE name binderType body info  =>
    let goal <- getMainGoal
    let (_, newGoal) ← goal.intro name
    logInfo m!"inForall name {name}"
    replaceMainGoal [newGoal]
    let names <- unfoldForall body
    return name :: names
  | _ =>
    logInfo m!"other"
    return []

elab "unfold_quotient"  : tactic => do
  let goal <- getMainGoal
  let goalType ← goal.getType
  logInfo m!"Goal: {goalType}"
  let names <- unfoldForall goalType
  evalTactic (<-`(tactic | vector_space_refold))

  for n in names do
    let id : TSyntax `ident := mkIdent n
    evalTactic (<- `(tactic | induction $id:ident using Quotient.ind))
  evalTactic (<- `(tactic | try unfold Quotient.lift₂))
  evalTactic (<- `(tactic | try unfold Quotient.lift))
