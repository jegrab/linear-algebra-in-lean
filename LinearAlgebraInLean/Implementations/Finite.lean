
import LinearAlgebraInLean.Group
import Mathlib.Data.Nat.Prime.Defs

open LinAlg

def Range (n: {n // n > 0}) := {x : Nat // x <n}
def RangeNonzero (n: {n // n > 0}) := {x : Nat // 0 < x ∧ x < n}

instance : Add (Range n) where
  add := fun ⟨a, _⟩ ⟨b, _ ⟩ =>
  have thm: (a + b) % n < n := by
    generalize a + b = x
    have := n.property
    rw [gt_iff_lt] at this
    apply Nat.mod_lt
    assumption
    ⟨(a + b) % n, thm⟩

instance (h: Nat.Prime n.val) :  Mul (RangeNonzero n) where
  mul := fun ⟨a, _⟩ ⟨ b, _⟩ =>
  have h₁: a * b % n.val > 0 := by
    by_contra hn
    simp [] at hn
    have :=Nat.dvd_of_mod_eq_zero hn
    have := (Prime.dvd_mul h.prime).mp this
    cases this
    . rename_i hha _ ha
      simp [Dvd.dvd] at ha
      have ⟨c, hc⟩ := ha
      rw [hc] at hha
      cases hha
      rename_i f g
      nth_rewrite 2 [<-Nat.mul_one n] at g
      rw [Nat.mul_lt_mul_left n.prop] at g
      have := Nat.ne_zero_of_mul_ne_zero_right (Nat.ne_of_gt f)
      have := Nat.zero_lt_of_ne_zero this
      cases c <;> contradiction
    . 

  have h₂ := sorry
  ⟨a * b % n, h₁ ∧ h₂⟩

instance CyclicGroup (n) : AbelianGroup (Range n) Add.add where
  assoc := by
    intro ⟨a, _⟩  ⟨ b, _⟩  ⟨ c, _⟩
    simp [Add.add]
    congr 2
    rw [Nat.add_assoc]
  commutative_law := by
    intro ⟨a, _⟩ ⟨b, _ ⟩
    simp [Add.add]
    congr 2
    rw [Nat.add_comm]
  neg := fun ⟨x, hx⟩ => ⟨(n - x) % n, Nat.mod_lt _ n.property⟩
  neutral := ⟨0, n.property⟩
  inverse_law_left := by
    intro ⟨a, _⟩
    simp [Add.add]
    congr
    rw [<-Nat.add_sub_assoc, Nat.add_sub_cancel_left, Nat.mod_self]
    apply Nat.le_of_lt
    assumption
  inverse_law_right := by
    intro ⟨a, _⟩
    simp [Add.add]
    congr
    rw [Nat.sub_add_cancel, Nat.mod_self]
    apply Nat.le_of_lt
    assumption
  neutral_left := by
    intro ⟨a, ah⟩
    simp [Add.add]
    congr
    rw [Nat.mod_eq]
    simp [n.property, Nat.le_of_lt ah]
    intro h
    have := Nat.not_le_of_gt ah
    contradiction
  neutral_right := by
    intro ⟨a, ah⟩
    simp [Add.add]
    congr
    rw [Nat.mod_eq]
    simp [n.property, Nat.le_of_lt ah]
    intro h
    have := Nat.not_le_of_gt ah
    contradiction

-- todo restrict on primes
instance CyclicMultGroup (n : {n: Nat //  n}): AbelianGroup (RangeNonzero n) where
