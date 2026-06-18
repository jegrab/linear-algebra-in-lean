import LinearAlgebraInLean.VectorSpace.Def
namespace LA.VectorSpace

variable [F: Field F] [V: VectorSpace F V]


theorem sum.perm {la lb: List F} (h: la.Perm lb): sum la = sum lb := by
  induction h with
   | nil => simp
   | cons x la ih => unfold sum; simp[ih]
   | trans => simp_all
   | swap x y l =>
    iterate 2 (unfold sum)
    iterate 2 rw [<-F.assoc]
    simp

theorem sum.push [S: AbelianGroup S] {a b: S}: sum ((a + b) :: ls) = sum (a :: b :: ls) := by
  unfold sum
  conv => rhs; unfold sum
  rw [<-S.assoc]


theorem sum.unzip [AbelianGroup S] {ls: List α} {f g: α -> S}: sum (List.map (fun x => f x + g x) ls) = sum (List.map f ls) + sum (List.map g ls) := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp
    rw [sum.push]
    unfold sum
    congr 1
    have {x: F} {l1 l2: List F}:  (x :: (l1 ++ l2)).Perm (l1 ++ (x :: l2)) := by
      apply List.perm_cons_append_cons
      rfl
    rw [<-sum.perm this]
    unfold sum
    congr 1
    simp [ih]


abbrev Span (vs: List V): VectorSpace F $ Subtype $
  (fun v: V => ∃ s: List F, s.length = vs.length ∧ v = sum (s.zipWith (. • .) vs))
  where
  add := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    exists a + b
    have ⟨sa, la, ha⟩ := ha
    have ⟨sb, lb, hb⟩ := hb
    exists sa.zipWith (. + .) sb
    simp[la, lb, <-List.map_uncurry_zip_eq_zipWith]
    rw [List.zip_map_left, List.map_map]
    unfold Function.comp
    unfold Function.uncurry
    simp
    rw [sum.unzip]
    congr
    . conv => rhs; rhs; lhs; (tactic => calc _ = Function.uncurry (. • .) ∘ (Prod.map Prod.fst id) := by unfold Function.comp; simp [Prod.map])
      rw [<-List.map_map, <-List.zip_map, List.map_fst_zip, List.map_id, List.map_uncurry_zip_eq_zipWith]
      assumption
      apply Nat.le_of_eq
      simp [la, lb]
    . conv => rhs; rhs; lhs; (tactic => calc _ = Function.uncurry (. • .) ∘ (Prod.map Prod.snd id) := by unfold Function.comp; simp [Prod.map])
      rw [<-List.map_map, <-List.zip_map, List.map_snd_zip, List.map_id, List.map_uncurry_zip_eq_zipWith]
      assumption
      apply Nat.le_of_eq
      simp [la, lb]
    
