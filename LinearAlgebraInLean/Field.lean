import LinearAlgebraInLean.Group


class Field (R : Type) [DecidableEq R] where
  add : operation R
  addStructure : AbelianGroup R add
  zero := addStructure.neutral
  _zero_is_addStructure_neutral : zero = addStructure.neutral := by simp
  mul : operation R
  mul_closed_zero: ∀ x y: R, (hx: x ≠ zero) -> (hy: y ≠ zero) -> mul x y ≠ zero
  _mul' : operation (nonzeros addStructure.toGroup) := fun a b => ⟨ mul a b, by grind⟩
  mul_eq_mul': ∀x y: R, (hx: x ≠ zero) ->  (hy: y ≠ zero) ->
    (_mul' ⟨x, by grind⟩ ⟨ y, by grind⟩).val = mul x y

  mulStructure : AbelianGroup (nonzeros addStructure.toGroup) _mul'
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

instance [DecidableEq R] (f : Field R) : Add R where
  add := f.add

instance [DecidableEq R] (f : Field R) : Mul R where
  mul := f.mul


instance RatField: Field Rat where
  add := Rat.add
  addStructure := RatAddGroup
  mul := (· * ·)
  mul_closed_zero := by
    intro a b ha hb
    have hx := (@Rat.mul_eq_zero a b).mp
    rw [<-Decidable.not_imp_not, <-@Classical.not_not (a = 0), <-@Classical.not_not (b = 0), <-Classical.not_and_iff_not_or_not, Classical.not_not] at hx
    apply hx
    apply And.intro <;> assumption

  mul_eq_mul' := by
    intro a b ha hb
    simp [rat_mul_non_zero, closed_nonzero]
    rfl


  mulStructure := RatMulGroup
  distributivity := by
    intro a b c
    change a * (b+c) = a * b + a * c
    apply Rat.mul_add
