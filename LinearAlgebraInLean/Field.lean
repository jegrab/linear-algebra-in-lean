import LinearAlgebraInLean.Group


class Ring (R: Type) extends AbelianGroup R, Mul R where
  mul_assoc: ∀ a b c: R, a * b * c = a * (b * c)
  distributivity : ∀ a b c : R , a  * (b + c) = (a * b) + (a * c)

attribute[simp] Ring.mul_assoc Ring.distributivity

class R1ng (R: Type) extends Ring R, One R where
  one_right: ∀ a: R, a * 1 = a
  one_left: ∀ a: R, 1 * a = a

attribute[simp] R1ng.one_right R1ng.one_left

class CommutativeRing (R: Type) extends Ring R where
  mul_comm: ∀ a b: R, a * b = b * a

attribute[simp] CommutativeRing.mul_comm

class Field (R : Type) extends CommutativeRing R, R1ng R, Inv (Group.non_zeros toGroup) where
  mul_inverse_left: ∀ (h: a ≠ 0), (⟨a,h⟩:(Group.non_zeros toGroup))⁻¹ * a = 1
  mul_inverse_right: ∀ (h:a ≠ 0), (a:R) * (⟨a,h⟩:(Group.non_zeros toGroup))⁻¹ = 1
  one_is_not_zero : (1: R) ≠ 0

attribute[simp] Field.mul_inverse_left Field.mul_inverse_right Field.one_is_not_zero

instance : CoeSort (Field R) Type where
  coe _ := R

instance [G: Field X]: OfNat (Group.non_zeros G.toGroup) (nat_lit 1) where
  ofNat := ⟨(1: G), by simp⟩

instance [R: Field R] : HDiv R R.non_zeros R where
  hDiv a b := a * b⁻¹
namespace Field

theorem inv_unique [F: Field F] (a: F) (h: a ≠ 0): unique (fun x => x * a = 1) := by
  unfold unique
  simp
  intro a₁ a₂ h₁ h₂
  let x : F.non_zeros := ⟨a, h⟩
  have := calc (x⁻¹).val
    _ = 1 * x⁻¹ := by simp
    _ = a₁ * a * x⁻¹ := by simp [h₁]
    _ = a₁ := by
      rw [Ring.mul_assoc]
      unfold x
      simp
  have := calc (x⁻¹).val
    _ = 1 * x⁻¹ := by simp
    _ = a₂ * a * x⁻¹ := by simp [h₂]
    _ = a₂ := by
      rw [Ring.mul_assoc]
      unfold x
      simp
  simp_all

@[simp] theorem one_inv_one [F: Field F]: (1: F.non_zeros)⁻¹ = (1: F) := by
  have h : neutral_pred (F.mul) F.one :=
  have := unique_neutral ()


theorem div_by_one [F: Field F] {a: F}: a / (1: F.non_zeros) = a := by
  simp [HDiv.hDiv]
  sorry

end Field

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
