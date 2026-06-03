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

end Sum

--
-- problems with list for indices:
--  need to define the vectors for all values that could be in the list, not only the ones that actually are
--
