import LinearAlgebraInLean.VectorSpace.LinearMap
import LinearAlgebraInLean.VectorSpace.Subspace
import LinearAlgebraInLean.VectorSpace.SubspaceLemmas
import LinearAlgebraInLean.VectorSpace.Kernel

namespace LA
namespace Image
variable  {F V} [F: Field F] [V: VectorSpace F V] [W: VectorSpace F W] {pred: V -> Prop} {U: Subspace V}

@[reducible] def image (φ: LinearMap V W) : Subspace W := by
  apply Subspace.mk (fun y => ∃ x : V, φ x = y)
  . constructor
    exists 0
    exists 0
    apply φ.zero
  . intro u v μ
    have ⟨u', hu⟩  := u.property
    have ⟨v', hv⟩  := v.property
    exists (μ • u' + v')
    simp_all


theorem whole_image_from_surjective {Φ: LinearMap V W} (h: Function.Surjective Φ): image Φ = W := by
  ext
  rename_i x
  simp
  exact h x

theorem surjective_from_whole_kernel {Φ: LinearMap V W} (h: image Φ = W): Function.Surjective Φ := by
  intro a
  rw [Subspace.ext_iff] at h
  rw [funext_iff] at h
  simp at h
  exact h a


theorem same_image_from_in_kernel {a b : V} {Φ: LinearMap V W} (h: a-b ∈ Kernel.kernel Φ): Φ a = Φ b := by
  sorry
