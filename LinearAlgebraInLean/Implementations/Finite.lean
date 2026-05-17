
import LinearAlgebraInLean.Group
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.GCD

open Group

abbrev NatPos := {n: Nat // n > 0}
def Range (n: NatPos) := {x : Nat // x <n}
def RangeNonzero (n: NatPos) := {x : Nat // 0 < x ∧ x < n}

instance : Add (Range n) where
  add := fun ⟨a, _⟩ ⟨b, _ ⟩ =>
  have thm: (a + b) % n < n := by
    generalize a + b = x
    have := n.property
    rw [gt_iff_lt] at this
    apply Nat.mod_lt
    assumption
    ⟨(a + b) % n, thm⟩

def mul {n: NatPos} (h: Nat.Prime n.val): operation (RangeNonzero n)  :=
  fun ⟨a, ha⟩ ⟨ b, hb⟩ => by
    exists (a * b) % n
    apply And.intro
    case right => simp [Nat.mod_lt _ n.property]
    suffices ¬ ↑n ∣ a * b by
     by_contra
     simp at this
     have := Nat.dvd_of_mod_eq_zero this
     contradiction
    have na :¬ ↑n ∣ a := by
      apply @Nat.not_dvd_of_lt_of_lt_mul_succ _ 0 <;> simp
      exact ha.left
      exact ha.right
    have nb :¬ ↑n ∣ b := by
      apply @Nat.not_dvd_of_lt_of_lt_mul_succ _ 0 <;> simp
      exact hb.left
      exact hb.right
    apply (Nat.Prime.dvd_mul h).not.mpr
    intro x
    cases x <;> contradiction

instance FiniteMul {n: NatPos} (h: Nat.Prime n.val) :  Mul (RangeNonzero n) where
  mul := mul h



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
instance CyclicMultGroup (n: NatPos) (h: Nat.Prime n.val): AbelianGroup (RangeNonzero n) (FiniteMul h).mul where
  neutral := by
    exists 1
    have := h.ne_one
    lia
  neg := fun ⟨x, hx⟩ => by
    exists (Nat.gcdA x n % n).toNat
    constructor
    suffices x.gcdA n % n ≠ 0 by
      have : x.gcdA n % n ≥ 0 := by
        have : (n: Int) ≠ 0 := by lia
        simp [@Int.emod_nonneg (x.gcdA n) n this]
      lia
    intro ha
    have := Int.dvd_of_emod_eq_zero ha

    --have := Nat.exists_mul_mod_eq_one_of_coprime -- todo
    have := Nat.gcd_eq_right_iff_dvd


    have := Nat.gcd_eq_gcd_ab x n
    have : x * (x.gcdA n) = (x.gcd n) - n * x.gcdB n := by lia




  commutative_law := by
    intro ⟨a, _, _⟩  ⟨b, _, _⟩
    simp [Mul.mul, mul]
    congr 2
    simp [Nat.mul_comm]
  assoc := by
    intro ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩
    simp [Mul.mul, mul]
    congr 2
    simp [Nat.mul_assoc]
  inverse_law_left := by
    intro ⟨a, _⟩
    simp [Mul.mul, mul]
    congr
