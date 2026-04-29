def neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

def operation (G: Type) := G -> G -> G

class Group (G: Type) (op : operation G) where
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

  nonzeros:= {x : G // x ≠ neutral}

class AbelianGroup (G: Type) (op : operation G) extends (Group G op) where
  commutative_law : ∀ a b : G, op a b = op b a

instance : AbelianGroup Int Int.add where
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
  commutative_law := Int.add_comm

instance : AbelianGroup Rat Rat.add where
  neg := Rat.neg
  neutral := 0
  assoc := Rat.add_assoc
  neutral_left := Rat.zero_add
  neutral_right := Rat.add_zero
  inverse_law_left := Rat.add_neg_cancel
  inverse_law_right := fun a => by
    have h := Rat.add_neg_cancel a
    rw [Rat.add_comm] at h
    exact h
  commutative_law := Rat.add_comm

-- instance [ag: AbelianGroup Rat Rat.add] : AbelianGroup ag.nonzeros

example [G: Group G op] : op (G.neutral) (G.neutral) = G.neutral := by
  apply Group.neutral_left
