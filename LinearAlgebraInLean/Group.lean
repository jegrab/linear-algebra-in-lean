def neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

class Group (G: Type) (op : G -> G -> G) where
  neg : G -> G
  neutral : G
  type : Type := G
  assoc : ∀ a b c : G , op (op a b) c = op a (op b c)

  neutral_left : ∀ a , op neutral a = a := (fun a => (neutral_law a).right)
  neutral_right : ∀ a : G , op a neutral = a := (fun a => (neutral_law a).left)
  neutral_law: neutral_pred op neutral := (fun a => ⟨neutral_right a, neutral_left a⟩)
  inverse_law_left : ∀ a : G, op a (neg a) = neutral
  inverse_law_right : ∀ a : G, op (neg a) a = neutral

  unique_neutral (ha : neutral_pred op a) : a = neutral := unique_neutral ha neutral_law

instance : Group Int Int.add where
  neg := Int.neg
  neutral := 0
  assoc := Int.add_assoc
  neutral_left := Int.zero_add
  neutral_right := Int.add_zero
  inverse_law_left := fun  a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    exact h
  inverse_law_right := fun a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    rw [Int.add_comm] at h
    exact h

example [G: Group G op] : op (G.neutral) (G.neutral) = G.neutral := by
  apply Group.neutral_left
