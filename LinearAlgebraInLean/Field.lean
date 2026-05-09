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
    (_mul' ⟨x, by grind⟩ ⟨y, by grind⟩).val = mul x y

  mulStructure : AbelianGroup (nonzeros addStructure.toGroup) _mul'
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

instance [DecidableEq R] (f : Field R) : Add R where
  add := f.add

instance [DecidableEq R] (f : Field R) : Mul R where
  mul := f.mul
