import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Subspace
import LinearAlgebraInLean.VectorSpace.SubspaceLemmas
namespace LA

namespace QuotientSpace

def relation (V: VectorSpace F V) (U : Subspace V) (a: V) (b: V) : Prop := a - b ∈ U

theorem relation_is_eqrel {V: VectorSpace F V} {U : Subspace V} : Equivalence (relation V U) := by
  constructor
  unfold relation
  . intro x
    simp
    exact Subspace.zero_in_subspace U
  . intro x y h
    unfold relation
    unfold relation at h
    let z := Subspace.closed (-1) h (Subspace.zero_in_subspace U)
    simp at z
    simp
    assumption
  . intro x y z hxy hyz
    unfold relation
    unfold relation at hxy hyz
    let z := Subspace.closed 1 hxy hyz
    simp at z
    rw [<-Group.assoc (-y)] at z
    simp at z
    simp
    assumption

end QuotientSpace

structure PreQuotientSpace (V: VectorSpace F V) (U : Subspace V) where
  rel := QuotientSpace.relation V U

attribute[simp] Subspace.add_is_add
attribute[instance] Subspace.toVectorSpace
