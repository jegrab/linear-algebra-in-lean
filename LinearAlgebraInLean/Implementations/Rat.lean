import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field
open Group

instance RatAddGroup : AbelianGroup Rat where
  op := Rat.add
  neutral := 0
  inv := Rat.neg
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
  op := rat_mul_non_zero
  inv := rat_inv_non_zero
  neutral := ⟨1, by simp⟩
  assoc := by
    intro ⟨a, ha⟩  ⟨ b, hb⟩  ⟨ c, hc⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.mul_assoc]
  neutral_left := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.one_mul]
  neutral_right := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.mul_one]
  inverse_right := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.mul_inv_cancel
    assumption
  inverse_left := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.inv_mul_cancel
    assumption
  comm := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [<-ret_non_zero_mul_is_mul]
    apply Rat.mul_comm

example (G: Group G) :  (𝟙: G) ◾ 𝟙 = 𝟙 := by
  apply Group.neutral_left

instance ℚ: Field Rat where
  add := Rat.add
  addStructure := RatAddGroup
  mul := (· * ·)
  mul_closed_zero := by
    intro a b ha hb
    have hx := (@Rat.mul_eq_zero a b).mp
    rw [<-Decidable.not_imp_not, <-@Classical.not_not (a = 0), <-@Classical.not_not (b = 0), <-Classical.not_and_iff_not_or_not, Classical.not_not] at hx
    apply hx
    apply And.intro <;> assumption

  mul_eq_mul' := by
    intro a b ha hb
    congr

  mulStructure := RatMulGroup
  distributivity := by
    intro a b c
    change a * (b+c) = a * b + a * c
    apply Rat.mul_add
