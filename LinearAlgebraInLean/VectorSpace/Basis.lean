import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.Sum
namespace LA.VectorSpace

variable [F: Field F] [V: VectorSpace F V]


-- set_option maxHeartbeats 100000
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
    rw [Sum.unzip]
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
  zero := by
    exists 0
    exists List.replicate vs.length 0
    constructor
    simp
    rw [<-List.map_const', List.zipWith_map_left, List.zipWith_self]
    simp
    rw [List.map_const', Sum.const_vs]
    simp
  neg := by
    intro ⟨x, hx⟩
    exists -x
    have ⟨sx, lx, hx⟩ := hx
    exists (-.) <$> sx
    constructor
    . simp [Functor.map, lx]
    simp [Functor.map, <-List.map_uncurry_zip_eq_zipWith, List.zip_map_left]
    unfold Function.uncurry
    unfold Function.comp
    simp
    have : (fun x: Prod F V => -(x.fst • x.snd)) = V.neg ∘ Function.uncurry V.smul := by unfold Function.uncurry; simp [Function.comp_def, SMul.smul_eq_hSMul]
    rw [this, <-List.map_map, Sum.neg, List.map_uncurry_zip_eq_zipWith, hx]
    congr

  smul := by
    intro μ ⟨v, hv⟩
    exists μ • v
    have ⟨sv, lv, hv⟩ := hv
    exists (μ * .) <$> sv
    constructor
    . simp [Functor.map, lv]
    simp [Functor.map, <-List.map_uncurry_zip_eq_zipWith, List.zip_map_left]
    unfold Function.uncurry
    unfold Function.comp
    simp
    have : (fun x: Prod F V => (μ * x.fst) • x.snd) = (μ • .) ∘ Function.uncurry V.smul := by unfold Function.uncurry; simp [Function.comp_def, SMul.smul_eq_hSMul]
    rw [this, <-List.map_map, Sum.scalar, List.map_uncurry_zip_eq_zipWith, hv]
    congr
