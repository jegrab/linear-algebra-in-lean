import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Util


class Rng (R: Type) extends AbelianGroup R, Mul R where
  mul_assoc: ∀ a b c: R, a * b * c = a * (b * c)
  distr_right : ∀ a b c : R , a  * (b + c) = (a * b) + (a * c)
  distr_left : ∀ a b c : R , (b + c) * a = (b * a) + (c * a)


attribute[simp] Rng.mul_assoc Rng.distr_left Rng.distr_right


class R1ng (R: Type) extends Rng R, One R where
  one_right: ∀ a: R, a * 1 = a
  one_left: ∀ a: R, 1 * a = a

attribute[simp] R1ng.one_right R1ng.one_left

class CommutativeRing (R: Type) extends Rng R where
  mul_comm: ∀ a b: R, a * b = b * a

attribute[simp] CommutativeRing.mul_comm

class Field (R : Type) extends CommutativeRing R, R1ng R, Inv (Group.non_zeros toGroup) where
  mul_inverse_left: ∀ (h: a ≠ 0), (⟨a,h⟩:(Group.non_zeros toGroup))⁻¹ * a = 1
  mul_inverse_right: ∀ (h:a ≠ 0), (a:R) * (⟨a,h⟩:(Group.non_zeros toGroup))⁻¹ = 1
  one_is_not_zero : (1: R) ≠ 0

attribute[simp] Field.mul_inverse_left Field.mul_inverse_right Field.one_is_not_zero

instance : CoeSort (Field R) Type where
  coe _ := R
instance : CoeSort (Rng R) Type where
  coe _ := R
instance : CoeSort (R1ng R) Type where
  coe _ := R

instance [G: Field X]: OfNat (Group.non_zeros G.toGroup) (nat_lit 1) where
  ofNat := ⟨(1: G), by simp⟩

instance [R: Field R] : HDiv R R.non_zeros R where
  hDiv a b := a * b⁻¹




namespace Field
variable [F: Field F]

theorem inv_unique {x a: F} (ha: a ≠ 0): a * x = 1 -> x = (⟨a, ha⟩: F.non_zeros)⁻¹ := by
  have (a:F) (h: a ≠ 0) : unique (fun x => a * x = 1) := by
    unfold unique
    simp
    intro a₁ a₂ h₁ h₂
    let x : F.non_zeros := ⟨a, h⟩
    have := calc (x⁻¹).val
      _ = 1 * x⁻¹ := by simp
      _ = a₁ * a * x⁻¹ := by simp [h₁]
      _ = a₁ := by
        rw [Rng.mul_assoc]
        unfold x
        simp
    have := calc (x⁻¹).val
      _ = 1 * x⁻¹ := by simp
      _ = a₂ * a * x⁻¹ := by simp [h₂]
      _ = a₂ := by
        rw [Rng.mul_assoc]
        unfold x
        simp
    simp_all
  intro h
  have := this a ha x ↑(⟨a,ha⟩: F.non_zeros)⁻¹ h (F.mul_inverse_right ha)
  assumption

@[simp] theorem zero_mul (a: F): 0 * a = 0 := by
  have := calc 0 * a
    _ = (0 + 0) * a := by simp
    _ = 0 * a + 0 * a := by rw [Rng.distr_left]
  have := Group.neutral_unique _ (0: F) (0 * a) (Group.neutral_left _) (this.symm)
  exact this.symm

@[simp] theorem mul_zero (a: F): a * 0 = 0 := by
 rw [CommutativeRing.mul_comm]
 apply Field.zero_mul

@[simp] theorem neg_mul (a: F): -1 * a = -a := by
  have : -1 * a + a = 0 := by calc
    _ = -1 * a + 1 * a := by simp
    _ = (-1 + 1) * a := by rw[Rng.distr_left]
    _ = 0 * a := by simp
    _ = 0 := by simp
  have := Group.neg_unique this
  have := congrArg F.neg this
  rw [Group.neg_neg] at this
  exact this.symm

theorem one_unique {e a: F} (ha: a ≠ 0) : e * a = a -> e = 1 := by
  have (a: F.non_zeros): unique (fun x: F => x * a = a) := by
    unfold unique
    intro b₁ b₂ h₁ h₂
    let ai := a⁻¹
    calc b₁
      _ = b₁ * 1 := by simp
      _ = b₁ * a * ai := by unfold ai; rw[Rng.mul_assoc, Field.mul_inverse_right a.property]
      _ = b₂ * a * ai := by simp [h₁, h₂]
      _ = b₂ * 1 := by unfold ai; rw [Rng.mul_assoc, Field.mul_inverse_right]
      _ = b₂ := by simp
  intro neutral
  exact this ⟨a, ha⟩ e 1 neutral (Field.one_left _)


@[simp] theorem inv_one: (1: F.non_zeros)⁻¹ = (1: F) := by
  have : (1:F) * 1 = 1 := by simp
  have inv_one_times_one: (1:F) * 1 = 1 := by simp
  have := Field.inv_unique (F.one_is_not_zero) inv_one_times_one
  apply Eq.symm
  assumption

theorem div_by_one {a: F}: a / (1: F.non_zeros) = a := by
  simp [HDiv.hDiv]

end Field

-- private def nat_to_field [f: R1ng R]: Nat -> R
--   | 0 => 0
--   | n + 1 => nat_to_field n + f.one

-- instance [f: Field R]: OfNat (R) n where
--   ofNat := nat_to_field n


structure RngHom (F: Rng F) (G: Rng G) extends GroupHom F.toGroup G.toGroup where
  mul: ∀ a b:F, hom (a * b) = hom a * hom b

structure R1ngHom (F: R1ng F) (G: R1ng G) extends RngHom F.toRng G.toRng where
  one: hom (1: F) = 1

def FieldHom (F: Field F) (G: Field G) := R1ngHom F.toR1ng G.toR1ng

attribute[simp] RngHom.mul R1ngHom.one


instance : CoeFun (RngHom F G) (λ_ => (F -> G)) where
  coe hom := hom.hom
instance : CoeFun (R1ngHom F G) (λ_ => (F -> G)) where
  coe hom := hom.hom

variable [F: Field F] [G: Field G]
instance : CoeFun (FieldHom F G) (λ_ => (F -> G)) where
  coe hom := hom.hom

theorem FieldHom.injective (hom: FieldHom F G) : Function.Injective hom := by
  unfold Function.Injective
  intro a b h
  let u := a - b
  have : hom u = 0 := by calc
    _ = hom a + hom (-b) := by simp[u]
    _ = hom a + -hom b := by simp
    _ = hom a - hom b := by simp
    _ = _ := by simp[h]
  suffices u = 0 by
    have := congrArg (. + b) this
    simp[u] at this
    calc a
     _ = a + 0 := by simp
     _ = a + b - b := by simp
     _ = b + a + -b := by simp
     _ = b + (a + -b) := by simp[<-F.assoc]
     _ = b := by simp[this]
  false_or_by_contra
  rename_i hu
  let u_inv: F := ↑(⟨u, by simp [hu]⟩: F.non_zeros)⁻¹
  have := calc
    1 = hom 1 := by simp
    _ = hom (u * u_inv) := by simp [u_inv]
    _ = hom u * hom u_inv := by simp
    _ = 0 := by simp [this]
  have := G.one_is_not_zero
  contradiction


theorem FieldHom.nonzero_nonzero (hom: FieldHom F G) (a: F.non_zeros): (hom ↑a) ≠ 0 := by
  have := hom.injective.ne a.property
  simp_all

@[simp] theorem FieldHom.inv (hom: FieldHom F G) (a: F.non_zeros): hom ↑(a⁻¹) = (⟨hom a, hom.nonzero_nonzero a⟩: G.non_zeros)⁻¹ := by
  have := calc  hom a * hom ↑(a⁻¹)
    _ = hom (a * a⁻¹) := by simp
    _ = 1 := by simp [F.mul_inverse_right]
  have := Field.inv_unique (hom.nonzero_nonzero a) this
  simp_all

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
