import LinearAlgebraInLean.Group


class Field (R : Type) where
  addStructure : AbelianGroup R
  add : operation R := addStructure.op
  _add_is_add : add = addStructure.op := by rfl
  zero := addStructure.default
  _zero_is_addStructure_neutral : zero = addStructure.default := by simp
  mul : operation R
  mul_closed_zero: ∀ x y: R, (hx: x ≠ zero) -> (hy: y ≠ zero) -> mul x y ≠ zero
  _mul' : operation (addStructure.toGroup.nonzeros) := fun a b => ⟨ mul a b, by grind⟩
  mul_eq_mul': ∀x y: R, (hx: x ≠ zero) ->  (hy: y ≠ zero) ->
    (_mul' ⟨x, by grind⟩ ⟨y, by grind⟩).val = mul x y

  mulStructure : AbelianGroup (addStructure.toGroup.nonzeros)
  one := mulStructure.default
  _one_is_mulStructure_neutral : one = mulStructure.default := by simp
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

instance [f : Field R] : Add R where
  add := f.add

instance  [f : Field R] : Mul R where
  mul := f.mul

instance [f: Field R]: OfNat (R) (nat_lit 0) where
  ofNat := f.zero

instance [f: Field R]: OfNat (R) (nat_lit 1) where
  ofNat := f.one

instance : CoeSort (Field R) Type where
  coe _ := R
