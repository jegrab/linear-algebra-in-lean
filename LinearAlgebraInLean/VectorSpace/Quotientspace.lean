import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Subspace
import LinearAlgebraInLean.VectorSpace.SubspaceLemmas
namespace LA

namespace QuotientSpace

def relation (V: VectorSpace F V) (U : Subspace V) (a: V) (b: V) : Prop := a - b ∈ U

--theorem tmp {V: VectorSpace F V} {U : Subspace V} (a : V) (h: a ∈ U): U.pred  :=

theorem relation_is_eqrel {V: VectorSpace F V} {U : Subspace V} : Equivalence (relation V U) := by
  constructor
  unfold relation
  . intro x
    simp
    exact Subspace.zero_in_subspace U
  . intro x y h
    unfold relation
    unfold relation at h
    have : -(x-y) ∈ U := by
      let d := Subtype.mk (x-y) h
      simp [Membership.mem] at d
      let d'  := -d
      simp [Membership.mem]
      have := d'.property
      simp [d', d] at this
      rw [Subspace.val_is_embed] at this
      simp at this
      unfold Subspace.embed at this
      simp at this
      exact this
    simp at this
    simp
    exact this
  . intro x y z hxy hyz
    sorry

end QuotientSpace


structure QuotienSpace (V: VectorSpace F V) (U : Subspace V) where
  from_def ::
  pred: V -> Prop
  toVectorSpace: VectorSpace F (Subtype pred)
  add_is_add: ∀ x y: Subtype pred, (↑(x + y): V) = ↑x + ↑y
  smul_is_smul: ∀ (μ : F) (v: Subtype pred), (↑(μ • v): V) = μ • ↑v

attribute[simp] Subspace.add_is_add
attribute[instance] Subspace.toVectorSpace
