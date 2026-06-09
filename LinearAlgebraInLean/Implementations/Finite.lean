
import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field
-- import LinearAlgebraInLean.Implementations.Int
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Logic.Lemmas

open LA.Group
namespace LA

def Cyclic (n: Nat): Setoid Int where
  r a b := ↑n ∣ (a - b)
  iseqv := {
    refl n := by simp
    symm h := by rw [<-Int.neg_sub, Int.dvd_neg]; assumption
    trans h₁ h₂ := by
      have := Int.dvd_add h₁ h₂
      simp [<-Int.add_sub_assoc] at this
      assumption
  }

-- instance instDecidableCyclic (n: Nat) (k r: Int): Decidable ((@instHasEquivOfSetoid _ (Cyclic n)).Equiv k r) := by
--   simp [HasEquiv.Equiv, instHasEquivOfSetoid]
--   unfold Setoid.r
--   simp [Cyclic]
--   apply Int.decidableDvd


def ℤ_mod (n: Nat) := Quotient (Cyclic n)
abbrev ℤ_mod.mk {n: Nat} (a: Int) := Quotient.mk (Cyclic n) a

instance CyclicGroup (n: Nat): AbelianGroup (ℤ_mod n) where
  add := Quotient.lift₂ (fun a b => ℤ_mod.mk (a + b)) <| by
      intros a₁ b₁ a₂ b₂ ha hb
      simp [ℤ_mod.mk, ℤ_mod, Cyclic]
      apply Quotient.sound
      simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r] at *
      rw [Int.sub_eq_add_neg, Int.neg_add]
      conv => rhs; tactic => (calc _ = (a₁ + -a₂) + (b₁ + -b₂) := by ac_rfl)
      simp [<-Int.sub_eq_add_neg]
      apply Int.dvd_add <;> assumption
  zero := ℤ_mod.mk 0
  neg := Quotient.lift (fun x => ℤ_mod.mk (n - x)) <| by
      intro a b h
      simp [ℤ_mod.mk, ℤ_mod, Cyclic]
      apply Quotient.sound
      simp [HasEquiv.Equiv, instHasEquivOfSetoid, Setoid.r] at *
      simp [Int.sub_eq_add_neg, Int.neg_add]
      conv => rhs; tactic => (calc _ = (n + -n) + (-a + b) := by simp [Int.add_comm])
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
    simp [Cyclic]
    simp [ℤ_mod.mk, Quotient.mk,  Quotient.lift]
    apply Quotient.sound
    simp [HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r
    simp [Cyclic]
  inverse_right := by
    intro a
    induction a using Quotient.ind
    simp [Quotient.mk, Quotient.lift]
    apply Quotient.sound
    simp [HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r
    simp[Cyclic]
    -- conv => rhs; rw [Int.sub_eq_add_neg, Int.add_comm, Int.add_assoc]; rhs; rw [Int.add_comm, <-Int.sub_eq_add_neg]
    -- simp
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

theorem ℤ_mod.zero_iff {n: Nat} [G: Group $ ℤ_mod n] (a: Int): ℤ_mod.mk a = (0: G) ↔ ↑n ∣ a := by
  sorry

instance Finite(n: Nat) (hp: Prime n): Field (ℤ_mod n) where
  one := ℤ_mod.mk 1
  mul := Quotient.lift₂ (fun a b => ℤ_mod.mk (a * b))  <| by
    intro a₁ b₁ a₂ b₂ ha hb
    unfold ℤ_mod.mk
    apply Quotient.sound
    simp_all [HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r at *
    simp [Cyclic] at *
    simp [Int.dvd_def] at ha hb
    obtain ⟨c₁, hc₁⟩ := ha
    obtain ⟨c₂, hc₂⟩ := hb
    have ha: a₁ = n * c₁ + a₂ := by lia
    have hb: b₁ = n * c₂ + b₂ := by lia
    simp [ha, hb, Int.mul_add, Int.add_mul, <-Int.mul_assoc, <-Int.add_assoc]
    ac_nf
    simp [<-Int.mul_assoc]
  inv := by
    simp [Group.non_zeros]
    intro ⟨a, ha⟩
    unfold ℤ_mod at *
    exists (λ x: _ -> _ => x ha) ∘ Quotient.hrecOn a (fun x h => ℤ_mod.mk (Int.gcdA x n)) <| by
      clear a ha
      intro b c h
      have := Quotient.sound h
      rw [this]
      apply Eq.heq
      funext (hc: ¬@ℤ_mod.mk n c = (0: CyclicGroup n))
      rw [<-ℤ_mod.mk, <-ℤ_mod.mk] at this
      have hb := this ▸ hc
      rw [ℤ_mod.zero_iff] at hc hb

      unfold ℤ_mod.mk
      apply Quotient.sound
      simp_all [HasEquiv.Equiv, instHasEquivOfSetoid]
      unfold Setoid.r at *
      simp [Cyclic] at *

      have bez_b := Int.gcd_eq_gcd_ab b n
      have : b.gcd n = 1 := by
        change Nat.Coprime _ _
        simp
        apply Nat.Coprime.symm
        apply (Nat.Prime.coprime_iff_not_dvd hp.nat_prime).mpr
        rwa [<-Int.natCast_dvd_natCast, Int.dvd_natAbs]
      rw [this] at bez_b
      have gcd_b: b * b.gcdA n = 1 - n * b.gcdB n := by lia

      have bez_c := Int.gcd_eq_gcd_ab c n
      have : c.gcd n = 1 := by
        change Nat.Coprime _ _
        simp
        apply Nat.Coprime.symm
        apply (Nat.Prime.coprime_iff_not_dvd hp.nat_prime).mpr
        rwa [<-Int.natCast_dvd_natCast, Int.dvd_natAbs]
      rw [this] at bez_c
      have gcd_c: c * c.gcdA n = 1 - n * c.gcdB n := by lia

      suffices ↑n ∣ c * (b * b.gcdA n) - b * (c * c.gcdA n) by
        conv at this => rhs; lhs; rw [<-Int.mul_assoc]; (conv => lhs; rw [Int.mul_comm]); rw [Int.mul_assoc]
        simp [<-Int.mul_sub] at this
        apply Int.dvd_of_dvd_mul_right_of_gcd_one
        apply Int.dvd_of_dvd_mul_right_of_gcd_one
        assumption
        have : ¬ n ∣ b.natAbs := by rwa [<-Int.natCast_dvd_natCast, Int.dvd_natAbs]
        apply (Nat.Prime.coprime_iff_not_dvd hp.nat_prime).mpr this
        have : ¬ n ∣ c.natAbs := by rwa [<-Int.natCast_dvd_natCast, Int.dvd_natAbs]
        apply (Nat.Prime.coprime_iff_not_dvd hp.nat_prime).mpr this

      rw [gcd_b, gcd_c]
      conv => (rhs; tactic => calc _ = c - b + n * (b * c.gcdB n - c * b.gcdB n) := by simp[Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg]; ac_nf; simp[<-Int.add_assoc]; ac_nf; congr 1; simp [Int.add_comm])
      apply Int.dvd_add
      . apply Int.dvd_neg.mp; simp; assumption
      . apply Int.dvd_mul_right











    sorry
