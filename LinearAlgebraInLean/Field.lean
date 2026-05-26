import LinearAlgebraInLean.Group


class Ring (R: Type) extends AbelianGroup R, Add R, Mul R where
  _group_op_is_add: Operation.op = (@Add.add R _) -- todo just use add syntax for group?
  mul_assoc: ∀ a b c: R, a * (b * c) = (a * b) * c
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

abbrev Ring.zero [R: Ring R] := R.neutral

class R1ng (R: Type) extends Ring R where
  one: R
  one_right: ∀ a: R, a * one = one
  one_left: ∀ a: R, one * a = one

class CommutativeRing (R: Type) extends R1ng R where
  commutative: ∀ a b: R, a * b = b * a

class Field (R : Type) extends CommutativeRing R where
  mul_inverse: R -> R
  mul_inverse_zero: mul_inverse zero = zero -- todo require this?
  mul_inverse_left: ∀ a ≠ zero, mul_inverse a * a = one
  mul_inverse_right: ∀ a ≠ zero, a * mul_inverse a = one

instance : CoeSort (Field R) Type where
  coe _ := R

-- abbrev Field.zero [Field F]: F := Ring.zero

private def nat_to_field [f: Field R]: Nat -> R
  | 0 => Ring.zero
  | n + 1 => nat_to_field n + f.one

instance [f: Field R]: OfNat (R) n where
  ofNat := nat_to_field n
