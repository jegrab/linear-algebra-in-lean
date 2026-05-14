
import LinearAlgebraInLean.Group
import Mathlib.Data.Nat.Prime.Defs

open LinAlg

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

instance foo {n: NatPos} (h: Nat.Prime n.val) :  Mul (RangeNonzero n) where
  mul := fun ⟨a, ha⟩ ⟨ b, hb⟩ => by
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
instance CyclicMultGroup (n: NatPos) (h: Nat.Prime n.val) [m: Mul (RangeNonzero n)]: AbelianGroup (RangeNonzero n) m.mul where
  neutral := by
    exists 1
    have := h.ne_one
    simp
  neg := fun ⟨x, hx⟩ => by
    exists n-x
    constructor
    apply (Nat.le_sub_iff_add_le (hx.right.le)).mpr
    grind
    grind
     -- todo
