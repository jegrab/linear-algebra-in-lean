import LinearAlgebraInLean.Group

def sum [Add t] [Zero t] (indices: List α) (values: α -> t) : t :=
  match indices with
  | [] => 0
  | i::is => values i + sum is values

namespace Sum
@[simp] theorem split [G: Group G] (ia: List α) (ib: List α) (v: α -> G) : sum ia v + sum ib v = sum (ia ++ ib) v := by
  induction ia with
  | nil =>
    unfold sum
    simp
  | cons i is ih =>
    simp [sum, ih]

theorem split_cons [G: Group G] (i1: α) (ia: List α) (v: α -> G) : sum (i1::ia) v = v  i1  + sum ia v := by
  conv =>
    lhs
    unfold sum

theorem swap_split [G: AbelianGroup G] (ia: List α) (ib: List α) (v: α -> G) : sum (ia ++ ib) v = sum (ib ++ ia) v := by
  rw [<-split, <-split]
  simp

theorem erase_then_add [G: AbelianGroup G] [BEq α] [LawfulBEq α] (is: List α) (i1: α) (v: α -> G) (h: is.contains i1 = true): sum (is.erase i1  ++ [i1]) v = sum is v := by
  induction is with
  | nil => contradiction
  | cons i is ih =>
    by_cases hi: i = i1
    . rw [hi]
      have : (i1::is).erase i1 = is := by
        unfold List.erase
        rw [BEq.refl]
      simp [this]
      rw [swap_split]
      simp
    . have hneq: (i == i1) = false := by
          simp
          intros hh
          apply hi
          exact hh
      have hneq_symm: (i1 == i) = false := by
        simp
        intros hh
        have hh := Eq.symm hh
        apply hi
        exact hh
      have hc: is.contains i1 = true := by
        unfold List.contains at h
        unfold List.elem at h-- make contains into elem
        simp [hneq_symm] at h
        simp [h]
      have ih := ih hc
      have hc : (i :: is).erase i1 = i :: (is.erase i1) := by
        conv =>
          lhs
          unfold List.erase
        simp [hneq]
      rw [hc]
      have hc: i :: is.erase i1 ++ [i1] = i :: (is.erase i1 ++ [i1]) := by
        simp
      rw [hc]
      simp [split_cons]
      rw [ih]

end Sum

--
-- problems with list for indices:
--  need to define the vectors for all values that could be in the list, not only the ones that actually are
--
