import LinearAlgebraInLean.Group

instance IntGroup : AbelianGroup Int := {
  op := Int.add
  inv := Int.neg
  default := 𝟙
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
}

-- set_option trace.Meta.synthInstance true
#eval (1: Int) ◾ 2
#eval (1: IntGroup) ◾ 2⁻¹
#check IntGroup.nonzeros
