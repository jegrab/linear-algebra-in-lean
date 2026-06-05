
import LinearAlgebraInLean.Group

open Group

instance Cyclic (n: Nat): Setoid Int where
  r a b := ↑n ∣ (a - b)
  iseqv := {
    refl n := by simp
    symm h := by rw [<-Int.neg_sub, Int.dvd_neg]; assumption
    trans h₁ h₂ := by
      have := Int.dvd_add h₁ h₂
      simp [<-Int.add_sub_assoc] at this
      assumption
  }

def ℤ_mod (n: Nat) := Quotient (Cyclic n)
abbrev ℤ_mod.mk {n: Nat} (a: Int) := Quotient.mk (Cyclic n) a

instance (n: Nat): AbelianGroup (ℤ_mod n) where
  add := Quotient.lift₂ (fun a b => ℤ_mod.mk (a + b)) <| by
      intros a₁ b₁ a₂ b₂ ha hb
      simp
      apply Quotient.sound
      simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r] at *
      rw [Int.sub_eq_add_neg, Int.neg_add]
      conv => rhs; tactic => (calc _ = (a₁ + -a₂) + (b₁ + -b₂) := by ac_rfl)
      simp [<-Int.sub_eq_add_neg]
      apply Int.dvd_add <;> assumption
  zero := ℤ_mod.mk 0
  neg := Quotient.lift (fun x => ℤ_mod.mk (n - x)) <| by
      intro a b h
      simp
      apply Quotient.sound
      simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r] at *
      simp [Int.sub_eq_add_neg, Int.neg_add]
      conv => rhs; tactic => (calc _ = (n + -n) + (-a + b) := by ac_rfl)
      simp [<-Int.sub_eq_add_neg]
      rw [<-Int.neg_neg (-a + b), Int.neg_add, Int.neg_neg, <-Int.sub_eq_add_neg]
      apply Int.dvd_neg.mpr
      assumption
  neutral_left := by
    intro a
    induction a using Quotient.ind
    simp [HAdd.hAdd]
    simp [ℤ_mod.mk, Quotient.mk, Quotient.lift₂, Quotient.lift]
    dsimp only [OfNat.ofNat, ℤ_mod.mk, Quotient.mk]
    simp [Add.add]

  neutral_right := by
    intro a
    induction a using Quotient.ind
    simp [HAdd.hAdd, ℤ_mod.mk, Quotient.mk, Quotient.lift₂, Quotient.lift]
    dsimp only [OfNat.ofNat, ℤ_mod.mk, Quotient.mk]
    simp [Add.add]
  inverse_left := by
    intro a
    induction a using Quotient.ind
    simp [ℤ_mod.mk, Quotient.mk,  Quotient.lift]
    apply Quotient.sound
    simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r]
  inverse_right := by
    intro a
    induction a using Quotient.ind
    simp [Quotient.mk, Quotient.lift]
    apply Quotient.sound
    simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r]
    conv => rhs; rw [Int.sub_eq_add_neg, Int.add_comm, Int.add_assoc]; rhs; rw [Int.add_comm, <-Int.sub_eq_add_neg]
    simp
  comm := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    simp [Quotient.mk, HAdd.hAdd, Quotient.lift₂, Quotient.lift]
    simp [Add.add, Int.add_comm]
  assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    simp [Quotient.mk, HAdd.hAdd, Quotient.lift₂, Quotient.lift]
    simp [Add.add, Int.add_assoc]
