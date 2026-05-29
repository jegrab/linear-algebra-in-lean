import LinearAlgebraInLean.Group


class Ring (R: Type) extends AbelianGroup R, Add R, Mul R where
  _group_op_is_add: Operation.op = (@Add.add R _) := by rfl -- todo just use add syntax for group?
  mul_assoc: ∀ a b c: R, a * b * c = a * (b * c)
  distributivity : ∀ a b c : R , a  * (b + c) = (a * b) + (a * c)

attribute [simp] Ring._group_op_is_add

instance [Ring R]: Zero R where
  zero := 𝟙

class R1ng (R: Type) extends Ring R, One R, Zero R where
  one_right: ∀ a: R, a * 1 = a
  one_left: ∀ a: R, 1 * a = a

class CommutativeRing (R: Type) extends R1ng R where
  commutative: ∀ a b: R, a * b = b * a

class Field (R : Type) extends CommutativeRing R, Inv R where
  mul_inverse_left: ∀ a ≠ 0, (a:R)⁻¹ * a = 1
  mul_inverse_right: ∀ a ≠ 0, (a:R) * a⁻¹ = 1
  mul_inverse_zero: ∀ a, (a: R) * 0 = 0 -- todo require this?

instance : CoeSort (Field R) Type where
  coe _ := R


private def nat_to_field [f: R1ng R]: Nat -> R
  | 0 => 0
  | n + 1 => nat_to_field n + f.one

instance [f: Field R]: OfNat (R) n where
  ofNat := nat_to_field n
