def existsUnique (p: T -> Prop) := ∃ x : T, (p x ∧ ∀ y : T, p y -> x = y)
open Lean.TSyntax.Compat in
macro "∃!" v:ident " : " t:term ", " b:term : term =>
  `(@existsUnique $t (fun $v => $b))

abbrev unique (pred: α -> Prop) := ∀ a b, pred a -> pred b -> a = b

theorem Zero.zero_is_zero [Zero X]: Zero.zero = (0: X) := by
  simp [OfNat.ofNat]

notation "(" x:10 "//" y ")" => (⟨x, y⟩ : Subtype _)

#check (5 // show (5 = 5) by omega)
#check (⟨5, show (5 = 5) by omega⟩ : Subtype _)
