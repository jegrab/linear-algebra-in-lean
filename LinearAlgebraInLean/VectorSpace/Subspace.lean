import LinearAlgebraInLean.VectorSpace.Def
namespace LA


structure Subspace (V: VectorSpace F V) where
  from_def ::
  pred: V -> Prop
  toVectorSpace: VectorSpace F (Subtype pred)
  add_is_add: ∀ x y: Subtype pred, (↑(x + y): V) = ↑x + ↑y
  smul_is_smul: ∀ (μ : F) (v: Subtype pred), (↑(μ • v): V) = μ • ↑v

attribute[simp] Subspace.add_is_add
attribute[instance] Subspace.toVectorSpace

-- instance [V: VectorSpace F V] (s: Subspace V): CoeDep (Subspace V) s (VectorSpace F $ Subtype s.pred) where
--   coe := s.toVectorSpace


instance : CoeSort (Subspace V) Type where
  coe x := Subtype x.pred

namespace Subspace
variable  {F V} [F: Field F] [V: VectorSpace F V] {pred: V -> Prop} {U: Subspace V}

#check U.toVectorSpace.zero

@[reducible] def mk (pred: V -> Prop)
  (inh: Nonempty $ Subtype pred)
  (closed: ∀ (u v: Subtype pred) (μ: F), pred $ μ • u + v)
  : Subspace V :=
  let subgroup := AbelianSubGroup pred inh <| by
    intro a b
    have := closed b a (-1)
    simp [AbelianGroup.comm, VectorSpace.smul_minus_left] at this
    apply this
  let smul μ v := by
      exists μ • v
      have h := closed v 0 μ
      simp [OfNat.ofNat, Zero.zero, subgroup] at h
      have : V.zero = (0: V) := by unfold OfNat.ofNat; unfold Zero.toOfNat0; simp
      rw [this] at h
      simp at h
      assumption
  {
    pred := pred
    toVectorSpace := {
      toAbelianGroup := subgroup
      smul := smul
      one_mul  := by
        intro ⟨v, hv⟩
        simp [HSMul.hSMul, smul]
        apply V.one_mul
      s_assoc := by
        intro μ γ ⟨c, hc⟩
        simp [HSMul.hSMul, smul]
        apply V.s_assoc
      s_distr_left := by
        intro μ γ ⟨v ,hv⟩
        simp [HSMul.hSMul, smul, HAdd.hAdd, subgroup, Add.add]
        apply V.s_distr_left
      s_distr_right := by
        intro μ ⟨u, hu⟩ ⟨v ,hv⟩
        simp [HSMul.hSMul, smul, HAdd.hAdd, subgroup, Add.add]
        apply V.s_distr_right
    }
    add_is_add := by simp [subgroup, HAdd.hAdd, Add.add]
    smul_is_smul := by simp [smul, HSMul.hSMul, SMul.smul]
  }




@[reducible] def zero_subspace: Subspace V := by
  apply Subspace.mk (. = (0: V))
  . constructor
    exists 0
  . intro ⟨u, hu⟩ ⟨v, hv⟩ μ
    simp [hu, hv]
