import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field

def sum [Add t] [Zero t] (indices: List t) : t :=
  match indices with
  | [] => 0
  | i::is => i + sum is

namespace Sum
@[simp] theorem split [G: Group G] (ia: List G) (ib: List G) : sum ia + sum ib = sum (ia ++ ib) := by
  induction ia with
  | nil =>
    unfold sum
    simp
  | cons i is ih =>
    simp [sum, ih]

theorem split_cons [G: Group G] (i1: G) (ia: List G) : sum (i1::ia) = i1  + sum ia := by
  conv =>
    lhs
    unfold sum

theorem swap_split [G: AbelianGroup G] (ia: List G) (ib: List G) : sum (ia ++ ib) = sum (ib ++ ia) := by
  rw [<-split, <-split]
  simp

theorem erase_then_add [G: AbelianGroup G] [BEq G] [LawfulBEq G] (is: List G) (i1: G) (h: is.contains i1) : sum (is.erase i1  ++ [i1]) = sum is := by
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


theorem erase_then_add_cons [G: AbelianGroup G] [BEq G] [LawfulBEq G] (i1: G) (is: List G) (h: is.contains i1 = true): sum (i1 :: is.erase i1) = sum is := by
  have : i1 :: is.erase i1 = [i1] ++ is.erase i1 := by simp
  rw [this]
  rw [swap_split]
  apply erase_then_add
  assumption

theorem perm [G: AbelianGroup G] (xs: List G) (ys: List G) (h: List.Perm xs ys) : sum xs = sum ys := by
  induction h with
  | nil => simp
  | cons x h1 h2 =>
    simp[split_cons,h2]
  | swap x y l =>
    simp[split_cons]
    rw[<-G.assoc,<-G.assoc,G.comm y x]
  | trans l1 l2 h1 h2 =>
    simp[h1,h2]

@[simp] theorem sum_distr[F: Field F] {is: List F} {x: F} : sum (List.map (fun i => x * i) is) = x * sum is := by
  induction is with
  | nil =>
    unfold sum
    simp
  | cons i iss ih =>
    unfold sum
    simp[ih]

theorem perm [S: AbelianGroup S] {la lb: List S} (h: la.Perm lb): sum la = sum lb := by
  induction h with
   | nil => simp
   | cons x la ih => unfold sum; simp[ih]
   | trans => simp_all
   | swap x y l =>
    iterate 2 (unfold sum)
    iterate 2 rw [<-S.assoc]
    simp

theorem push [S: AbelianGroup S] {a b: S}: sum ((a + b) :: ls) = sum (a :: b :: ls) := by
  unfold sum
  conv => rhs; unfold sum
  rw [<-S.assoc]


theorem unzip [AbelianGroup S] {ls: List α} {f g: α -> S}: sum (List.map (fun x => f x + g x) ls) = sum (List.map f ls) + sum (List.map g ls) := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp
    rw [push]
    unfold sum
    congr 1
    have {x: S} {l1 l2: List S}:  (x :: (l1 ++ l2)).Perm (l1 ++ (x :: l2)) := by
      apply List.perm_cons_append_cons
      rfl
    rw [<-perm this]
    unfold sum
    congr 1
    simp [ih]

theorem const [R1ng S] {a: S}: sum (List.replicate n a) = n * a := by
  induction n with
    | zero => simp [sum, nat_to_r1ng]
    | succ n h =>
      unfold List.replicate
      simp [nat_to_r1ng]
      unfold sum
      rw [h, One.one_is_ofNat]
      simp

theorem neg [S: AbelianGroup S] {ls: List S}: sum (List.map S.neg ls) = - sum ls := by
  induction ls with
    | nil => simp [sum]
    | cons x ll ih =>
      unfold List.map
      unfold sum
      simp [ih]



end Sum

--
-- problems with list for indices:
--  need to define the vectors for all values that could be in the list, not only the ones that actually are
--
