import LinearAlgebraInLean.Group


class Field (R : Type) [DecidableEq R] where
  add : operation R
  addStructure : AbelianGroup R add
  mul_ : operation (nonzeros addStructure.toGroup)
  --mul : operation R := fun a b => by
  --  by_cases ha: a = addStructure.neutral
  --  exact addStructure.neutral
  --  by_cases hb : b = addStructure.neutral
  --  exact addStructure.neutral
  --  exact (mul_ ⟨a, ha⟩ ⟨b, hb ⟩).val
  mul : operation R := fun a b => by
    cases ha: decide (a ≠  addStructure.neutral)
    exact addStructure.neutral
    cases hb : decide (b ≠  addStructure.neutral)
    exact addStructure.neutral
    exact (mul_ ⟨a, of_decide_eq_true ha⟩ ⟨b, of_decide_eq_true hb ⟩).val

  mulStructure : AbelianGroup (nonzeros addStructure.toGroup) mul_
  distributivity : ∀ a b c : R , mul a (add b c) = add (mul a b) (mul a c)

instance [DecidableEq R] (f : Field R) : Add R where
  add := f.add

instance [DecidableEq R] (f : Field R) : Mul R where
  mul := f.mul

instance : Field Rat where
  add := Rat.add
  addStructure := RatAddGroup
  mul_ := rat_mul_non_zero
  mulStructure := RatMulGroup
  distributivity := by
    intro a b c
    by_cases ha : a = RatAddGroup.neutral
    simp [ha, RatAddGroup.neutral_left]
    simp [ha]
    by_cases hbc : b.add c = RatAddGroup.neutral
    by_cases hb : b = RatAddGroup.neutral
    by_cases hc : c = RatAddGroup.neutral
    simp [hbc, hb,hc, RatAddGroup]
    by_cases h: Rat.add 0 0 = 0
    simp [h]
    have x: Rat.add 0 0 = 0 := by apply Rat.add_zero
    contradiction
    simp [hb]
    have x : RatAddGroup.neutral.add c = c := by apply Rat.zero_add
    simp [x, hc, RatAddGroup, rat_mul_non_zero, closed_nonzero]
    have y: Rat.add 0 c = c := by apply Rat.zero_add
    have z : c ≠  0 := by apply hc
    simp [y, z]
    have u : Rat.add 0 (a.mul c) = a.mul c := by apply Rat.zero_add
    rw [u]
    simp [hbc, hb]
    by_cases hc : c = RatAddGroup.neutral
    rw [hc] at hbc
    have abc' : b + 0 = 0 := by apply hbc
    have hb' : b = 0 := by
      rw [Rat.add_zero] at abc'
      assumption
    contradiction
    simp [hc, rat_mul_non_zero, closed_nonzero]
    have g : 0 = (a * b) + (a * c) := by
      rw [<-Rat.mul_add]
      have x : b + c = 0 := hbc
      rw [x]
      simp
    apply g
    simp [hbc, rat_mul_non_zero, closed_nonzero]
    by_cases hb : b = RatAddGroup.neutral
    by_cases hc : c = RatAddGroup.neutral
    have hbpc : b + c = 0 := by
      have z : 0 = RatAddGroup.neutral := by rfl
      simp [hb,hc, <-z,Rat.add_zero]
    contradiction
    have z : 0 = RatAddGroup.neutral := by rfl
    have nc : c ≠ 0 := by apply hc
    simp [hb,<-z, nc]
    have x: Rat.add 0 c = c := by apply Rat.zero_add
    simp [x]
    have x: Rat.add 0 (a.mul c) = a.mul c := by apply Rat.zero_add
    simp [x]

    simp [hb]
    have z : 0 = RatAddGroup.neutral := by rfl
    by_cases hc : c = RatAddGroup.neutral
    simp [hc, <-z]
    have x : (b.add 0) = b := by apply Rat.add_zero
    have y : ((a.mul b).add 0) = (a.mul b) := by apply Rat.add_zero
    simp [x,y]
    simp [hc]
    apply Rat.mul_add
