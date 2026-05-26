import LinearAlgebraInLean.Group

instance IntGroup : AbelianGroup Int := {
  op := Int.add
  inv := Int.neg
  neutral := 0
  assoc := Int.add_assoc
  neutral_left := Int.zero_add
  neutral_right := Int.add_zero
  inverse_right := fun  a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    exact h
  inverse_left := fun a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    rw [Int.add_comm] at h
    exact h
  comm := Int.add_comm
}

-- set_option trace.Meta.synthInstance true
#eval (1: Int) ◾ 2
#eval (1: IntGroup) ◾ 2⁻¹
#check IntGroup.Group.non_neutrals

def Even (i: Int) := ∃k: Int, 2 * k = i

instance EvenIntGroup : AbelianGroup (Subtype Even) := by
  apply AbelianSubGroup
  · exact {
    default := by
      exists 0
      unfold Even
      exists 0
  }
  · intro ⟨a, ⟨x, hx⟩⟩ ⟨b,⟨y, hy⟩⟩
    unfold Even
    simp
    exists x - y
    rw [Int.mul_sub]
    simp [hx, hy, Operation.op, Inv.inv]
    rfl

def tripple := {
  hom:= fun x => 3 * x
  property := by
    intro a b
    simp [Operation.op, Int.mul_add]
  :GroupHom IntGroup.toGroup IntGroup.toGroup
}

#eval tripple 2
