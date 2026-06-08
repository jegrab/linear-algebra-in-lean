import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field
namespace LA
open Group

instance RatAddGroup : AbelianGroup Rat where
  add := Rat.add
  zero := 0
  neg := Rat.neg
  assoc := Rat.add_assoc
  neutral_left := Rat.zero_add
  neutral_right := Rat.add_zero
  inverse_left := Rat.neg_add_cancel
  inverse_right := Rat.add_neg_cancel
  comm := Rat.add_comm



#check Rat.mul_eq_zero.mp
-- set_option pp.all true
def rat_mul_non_zero := closed_nonzero Rat.mul x
  where x : ∀ a b : Rat,  a = 0 ∨ b = 0 ↔ a * b = 0 := fun a b => (@Rat.mul_eq_zero a b).symm


def nonzero_rat := { x : Rat // x ≠ 0}
instance : Mul nonzero_rat where
  mul := rat_mul_non_zero

theorem ret_non_zero_mul_is_mul (a b : Rat) (ha: a ≠ 0) (hb : b ≠ 0) : (⟨ a * b, (rat_mul_non_zero ⟨a, ha ⟩  ⟨b,hb⟩).property⟩: nonzero_rat)  = (rat_mul_non_zero ⟨a, ha⟩ ⟨b, hb⟩) := by
  simp [rat_mul_non_zero, closed_nonzero]
  rfl

theorem rat_inv_injective: Function.Injective Rat.inv := by
    unfold Function.Injective
    intro a b
    intro h
    rw [<-Rat.inv_inv a, <- Rat.inv_inv b]
    simp [Inv.inv]
    apply congrArg Rat.inv
    assumption

theorem inv_not_zero (x : Rat) (h : x ≠ 0) : x.inv ≠ 0 := by
  apply rat_inv_injective.ne_iff.mp
  have : ∀ x:Rat, x.inv.inv = x := Rat.inv_inv
  rw [this]
  have : (0:Rat).inv = 0 := Rat.inv_zero
  rw [this]
  assumption


def rat_inv_non_zero (x: nonzero_rat) : nonzero_rat := by
  let ⟨x, h⟩ := x
  let r := Rat.inv x
  exact ⟨r, inv_not_zero x h⟩

variable (a : Rat) (ha: a ≠ 0)
#check (rat_inv_non_zero ⟨a, ha ⟩).property

theorem rat_non_zero_inv_is_inv (a : Rat) (ha: a ≠ 0) : (⟨ Rat.inv a, inv_not_zero a ha ⟩: nonzero_rat)  = (rat_inv_non_zero ⟨a, ha⟩) := by
  simp [rat_inv_non_zero]

instance RatMulGroup : AbelianGroup { x : Rat // x ≠ 0} where
  add := rat_mul_non_zero
  neg := rat_inv_non_zero
  zero := ⟨1, by simp⟩
  assoc := by
    intro ⟨a, ha⟩  ⟨ b, hb⟩  ⟨ c, hc⟩
    simp [HAdd.hAdd,<-ret_non_zero_mul_is_mul, Rat.mul_assoc]
  neutral_left := by
    intro ⟨a, ha⟩
    simp [HAdd.hAdd, OfNat.ofNat, rat_mul_non_zero, closed_nonzero]
    change 1 * a = a
    simp
  neutral_right := by
    intro ⟨a, ha⟩
    simp [HAdd.hAdd, OfNat.ofNat, <-ret_non_zero_mul_is_mul]
    change a * 1 = a
    simp
  inverse_right := by
    intro ⟨a, ha⟩
    simp [HAdd.hAdd, OfNat.ofNat,<-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.mul_inv_cancel
    assumption
  inverse_left := by
    intro ⟨a, ha⟩
    simp [HAdd.hAdd, OfNat.ofNat, <-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.inv_mul_cancel
    assumption
  comm := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [HAdd.hAdd, OfNat.ofNat, <-ret_non_zero_mul_is_mul]
    apply Rat.mul_comm

example (G: Group G) :  (0: G) + 0 = 0 := by
  apply Group.neutral_left

theorem _root_.Rat.inv_zero_iff_zero {a: Rat}: a⁻¹ = 0 ↔ a = 0 := by
  constructor
  . simp [Rat.inv_def]
    intro h
    simp [Rat.divInt] at h
    cases ha: a.num <;> try simp[ha] at h <;> rename_i a_num
    . have := a.den_nz
      simp [Rat.mkRat_def] at h
      have : a_num = 0 := by
        false_or_by_contra
        simp_all
      apply Rat.eq_iff_mul_eq_mul.mpr
      simp [ha, this]
    . have := a.den_nz
      contradiction
  . intro ha
    rw [ha]
    simp

instance ℚ: Field Rat :=
  let := RatAddGroup
  {
    toAbelianGroup := this
    mul := Rat.mul
    mul_assoc := Rat.mul_assoc
    distr_left := by
      have := Rat.add_mul
      simp_all [HAdd.hAdd]
    distr_right := Rat.mul_add
    mul_comm := Rat.mul_comm
    one := 1
    one_is_not_zero := by simp
    one_right := Rat.mul_one
    one_left := Rat.one_mul
    inv := fun ⟨a, ha⟩ => by
      exists a⁻¹
      intro h
      have := a.inv_zero_iff_zero.mp h
      contradiction
    mul_inverse_left := Rat.inv_mul_cancel _
    mul_inverse_right := Rat.mul_inv_cancel _
  }
