import LinearAlgebraInLean.Group


class Field (R : Type) where
  addStructure : AbelianGroup R
  add : operation R := addStructure.op
  _add_is_add : add = addStructure.op := by rfl
  zero := addStructure.neutral
  _zero_is_addStructure_neutral : zero = addStructure.neutral := by simp
  mul : operation R
  mul_closed_zero: ∀ x y: R, (hx: x ≠ zero) -> (hy: y ≠ zero) -> mul x y ≠ zero
  _mul' : operation (addStructure.toGroup.nonzeros) := fun a b => ⟨ mul a b, by grind⟩
  mul_eq_mul': ∀x y: R, (hx: x ≠ zero) ->  (hy: y ≠ zero) ->
    (_mul' ⟨x, by grind⟩ ⟨y, by grind⟩).val = mul x y

  mulStructure : AbelianGroup (addStructure.toGroup.nonzeros)
  one := mulStructure.neutral
  _one_is_mulStructure_neutral : one = mulStructure.neutral := by simp
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

instance [f : Field R] : Add R where
  add := f.add

instance  [f : Field R] : Mul R where
  mul := f.mul

private def nat_to_field [f: Field R]: Nat -> R
  | 0 => f.zero
  | n + 1 => nat_to_field n + f.one

instance [f: Field R]: OfNat (R) n where
  ofNat := nat_to_field n


instance : CoeSort (Field R) Type where
  coe _ := R
