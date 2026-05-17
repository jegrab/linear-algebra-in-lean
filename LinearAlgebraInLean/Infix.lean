
import Lean
open Lean
syntax:73 (name := infixop) term:73 "§" term:74 "§" term:73 : term

@[macro infixop] def lxorImpl : Macro
  | `($l:term § $f:term § $r:term) => `($f ($l) ($r))
  | _ => Macro.throwUnsupported

#check 2 §Add.add§ 3 §Add.add§ 4 * 2
#check ∀ a b: Nat, a §Add.add§ b = b §Add.add§ a
