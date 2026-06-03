import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Util


class Ring (R: Type) extends AbelianGroup R, Mul R where
  mul_assoc: ∀ a b c: R, a * b * c = a * (b * c)
  distr_right : ∀ a b c : R , a  * (b + c) = (a * b) + (a * c)
  distr_left : ∀ a b c : R , (b + c) * a = (b * a) + (c * a)

namespace Ring
variable [Ring R]

@[simp] theorem zero_mul (a: R): 0 * a = 0 := by
  have := calc 0 * a
    _ = (0 + 0) * a := by simp
    _ = 0 * a + 0 * a := by rw [Ring.distr_left]
  have := Group.eq_zero_of_add_eq_self (Eq.symm this)
  exact this

@[simp] theorem mul_zero (a: R): a * 0 = 0 := by
  have := calc a * 0
    _ = a * (0 + 0) := by simp
    _ = a * 0 + a*0 := by rw [Ring.distr_right]
  have := Group.eq_zero_of_add_eq_self (Eq.symm this)
  exact this


theorem mul_both_right {a b: R} (x: R) (h: a = b): a*x = b*x := by simp[h]
theorem mul_both_left {a b: R} (x: R) (h: a = b): x*a = x*b := by simp[h]

@[simp] theorem put_neg_out_of_mul_left {a b: R}: -a*b = -(a*b) := by
  have : a + -a = 0 := by simp
  have : (a + -a)*b = 0*b := mul_both_right b this
  have : a *b + -a * b = 0 := by simp[<-distr_left]
  have : -a * b = -(a * b) := Group.move_left this
  assumption

@[simp] theorem put_neg_out_of_mul_right {a b: R}: a*-b = -(a*b) := by
  have : b + -b = 0 := by simp
  have : a*(b + -b) = a*0 := mul_both_left a this
  have : a *b + a * -b = 0 := by simp[<-distr_right]
  have : a * -b = -(a * b) := Group.move_left this
  assumption

end Ring


attribute[simp] Ring.mul_assoc Ring.distr_left Ring.distr_right


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
variable [F: Field F]

theorem inv_unique (a: F) (h: a ≠ 0): unique (fun x => x * a = 1) := by
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

@[simp] theorem neg_mul (a: F): -1 * a = -a := by
  have : -1 * a + a = 0 := by calc
    _ = -1 * a + 1 * a := by simp
    _ = (-1 + 1) * a := by rw[Ring.distr_left]
    _ = 0 * a := by simp
    _ = 0 := by simp
  have := Group.inv_unique a (-1 * a) (-a) this (Group.inverse_left _)
  exact this

theorem one_unique (a: F.non_zeros): unique (fun x: F => x * a = a) := by
  unfold unique
  intro b₁ b₂ h₁ h₂
  let ai := a⁻¹
  calc b₁
    _ = b₁ * 1 := by simp
    _ = b₁ * a * ai := by unfold ai; rw[Ring.mul_assoc, Field.mul_inverse_right a.property]
    _ = b₂ * a * ai := by simp [h₁, h₂]
    _ = b₂ * 1 := by unfold ai; rw [Ring.mul_assoc, Field.mul_inverse_right]
    _ = b₂ := by simp


@[simp] theorem inv_one: (1: F.non_zeros)⁻¹ = (1: F) := by
  have : (1:F) * 1 = 1 := by simp
  have inv_one_times_one: ((1:F.non_zeros)⁻¹.val) * 1 = 1 := by
    apply mul_inverse_left
  have := Field.inv_unique (1: F) F.one_is_not_zero (1: F.non_zeros) (1: F.non_zeros)⁻¹.val this inv_one_times_one
  apply Eq.symm
  assumption

theorem div_by_one {a: F}: a / (1: F.non_zeros) = a := by
  simp [HDiv.hDiv]

-- mul_inverse_right: ∀ (h:a ≠ 0), (a:R) * (⟨a,h⟩:(Group.non_zeros toGroup))⁻¹ = 1
theorem move_inverse (x: F.non_zeros)(h: a = (x⁻¹).val * b) : x.val * a = b := by
  rw[h, <-Ring.mul_assoc]
  have ⟨a, ha⟩ := x
  simp

theorem move_inverse_back (x: F.non_zeros)(h: x.val * a = b) : a = (x⁻¹).val * b:= by
  rw[<-h, <-Ring.mul_assoc]
  have ⟨a, ha⟩ := x
  simp

theorem remove_both_sides_left (x: F.non_zeros) (h: x.val * a = x.val *b) : a = b := by
  have h : x⁻¹.val * (x.val * a) = x⁻¹.val * (x.val *b) := by rw[h]
  rw [<-Ring.mul_assoc,<-Ring.mul_assoc] at h
  have ⟨a,ha ⟩:=x
  simp at h
  assumption

end Field

-- private def nat_to_field [f: R1ng R]: Nat -> R
--   | 0 => 0
--   | n + 1 => nat_to_field n + f.one

-- instance [f: Field R]: OfNat (R) n where
--   ofNat := nat_to_field n


structure FieldHom (F: Field F) (G: Field G) extends GroupHom F.toGroup G.toGroup where
  mul: ∀ a b:F, hom (a * b) = hom a * hom b

attribute[simp] FieldHom.mul

variable [F: Field F] [G: Field G]

instance : CoeFun (FieldHom F G) (λ_ => (F -> G)) where
  coe hom := hom.hom


@[simp] theorem FieldHom.one (hom: FieldHom F G): hom 1 = 1 := by
  apply Eq.symm
  have: hom 1 = hom 1 * hom 1 := by calc hom 1
    _ = hom (1 * 1) := by simp
    _ = hom 1 * hom 1 := by simp[<-hom.mul]
  apply Field.inv_unique
  all_goals sorry



-- todo
-- @[simp] theorem FieldHom.inv (hom: FieldHom F G) (a: F.non_zeros): hom (a⁻¹) = (hom a)⁻¹ := by
--   have := calc hom (a⁻¹) + hom a
--     _ = hom (a⁻¹ * a) := by simp [<-hom.mul]
--     _ = 1 := by simp
--   have := Field.inv_unique (hom a) (hom a)⁻¹ (hom a⁻¹)
--   simp_all

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
