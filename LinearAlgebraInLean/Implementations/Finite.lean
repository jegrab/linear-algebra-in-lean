
import LinearAlgebraInLean.Group

def Range (n: {n // n > 0}) := {x : Nat // x <n}

instance : Add (Range n) where
  add := fun ⟨a, _⟩ ⟨b, _ ⟩ =>
  let thm: (a + b) % n < n := by
    generalize a + b = x
    have := n.property
    rw [gt_iff_lt] at this
    apply Nat.mod_lt
    assumption
    ⟨(a + b) % n, thm⟩

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
