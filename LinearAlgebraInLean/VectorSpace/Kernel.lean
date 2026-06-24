import LinearAlgebraInLean.VectorSpace.LinearMap
import LinearAlgebraInLean.VectorSpace.Subspace
import LinearAlgebraInLean.VectorSpace.SubspaceLemmas

namespace LA
namespace Kernel
variable  {F V} [F: Field F] [V: VectorSpace F V] [W: VectorSpace F W] {pred: V -> Prop} {U: Subspace V}

@[reducible] def kernel (φ: LinearMap V W) : Subspace V := by
  apply Subspace.mk (fun x => φ x = 0)
  . constructor
    exists 0
    apply φ.zero
  . intro u v μ
    simp [u.property, v.property]

theorem zero_kernel_from_injective {Φ: LinearMap V W} (h: Function.Injective Φ): kernel Φ = Subspace.zero_subspace := by
  apply Subspace.eq_zero_from_pred
  intro x hx
  simp_all
  apply h
  simp
  assumption

theorem injective_from_zero_kernel {Φ: LinearMap V W} (h: kernel Φ = Subspace.zero_subspace): Function.Injective Φ := by
  unfold Function.Injective
  intro a b h_ab
  have : (kernel Φ).pred (a-b) := by simp[h_ab]
  rw[h] at this
  simp at this
  let this := Group.neg_unique_left this
  simp[this]
