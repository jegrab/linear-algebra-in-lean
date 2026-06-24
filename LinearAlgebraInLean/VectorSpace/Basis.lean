import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.Sum
import LinearAlgebraInLean.VectorSpace.Subspace
namespace LA.VectorSpace

variable [F: Field F] [V: VectorSpace F V]

abbrev Span (F: Field F) [V: VectorSpace F V] (vs: List V): Subspace V := by
  apply Subspace.mk (fun v: V => ∃ s: List F, s.length = vs.length ∧ v = sum (s.zipWith (. • .) vs))
  . constructor
    exists 0
    exists List.replicate vs.length 0
    constructor
    simp
    rw [<-List.map_const', List.zipWith_map_left, List.zipWith_self]
    simp
    rw [List.map_const', Sum.const_vs]
    simp
  . intro ⟨x, sx, lx, hx⟩ ⟨y, sy, ly, hy⟩ μ
    simp
    exists List.map (fun (x,y) =>  μ * x + y) $ sx.zip sy
    constructor
    . simp[lx, ly]
    simp[<-List.map_uncurry_zip_eq_zipWith]
    rw [List.zip_map_left, List.map_map]
    unfold Function.comp
    unfold Function.uncurry
    simp
    rw [Sum.unzip]
    congr
    . conv => rhs; rhs; lhs; (tactic => calc _ = Function.uncurry V.smul ∘ (Prod.map Prod.snd id) := by simp [Function.comp_def]; simp [Prod.map, <-SMul.smul_eq_hSMul])
      rw [<-List.map_map, <-List.zip_map, List.map_id, List.map_snd_zip, List.map_uncurry_zip_eq_zipWith]
      rwa [SMul.smul_eq_hSMul]
      apply Nat.le_of_eq
      simp [lx, ly]
    . conv => rhs; rhs; lhs; ext; rw [<-VectorSpace.s_assoc]
      conv => rhs; rhs; lhs; (tactic => rename_i x; calc _ = (μ • .) ∘ Function.uncurry SMul.smul ∘ Prod.map Prod.fst id := by unfold Function.uncurry; unfold Prod.map; unfold Function.comp; simp[SMul.smul_eq_hSMul] )
      rw [<-List.map_map, Sum.scalar]
      congr
      rw [<-List.map_map, <-List.zip_map, List.map_id, List.map_fst_zip, List.map_uncurry_zip_eq_zipWith]
      rwa [SMul.smul_eq_hSMul]
      apply Nat.le_of_eq
      simp [lx, ly]


def Basis (V: VectorSpace F V) (vs: List V) := Span F vs = V ∧ VectorSpace.linear_independent F vs
