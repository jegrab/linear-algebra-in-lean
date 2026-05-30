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
  mul_comm: ∀ a b: R, a * b = b * a

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


-- instance FieldOfTwoGroups [DecidableEq R] [add: AbelianGroup R] [mul: AbelianGroup add.non_neutrals] (dist: ∀ a b c: add.non_neutrals, a §add.op§ (b §mul.op§ c) = (a §mul.op§ b) §add.op§ (a §mul.op§ c))
-- : Field R :=
--   let mul_fn : Mul R := {
--     mul := by
--       intro a b
--       by_cases a ≠ 𝟙 <;> by_cases b ≠ 𝟙
--       . exact (mul.op ⟨a, by assumption⟩ ⟨b, by assumption⟩).val
--       all_goals exact 𝟙
--   }
--   {
--     toAbelianGroup := add
--     add := add.op
--     zero := 𝟙
--     toMul := mul_fn
--     one := mul.neutral
--     inv := by
--       intro a
--       by_cases a = 𝟙
--       . exact 𝟙
--       . exact (mul.groupInv ⟨a, by assumption⟩).val
--     _group_op_is_add := rfl
--     one_left := by
--       intro a
--       by_cases a = 𝟙












--   : Field R
--   }
