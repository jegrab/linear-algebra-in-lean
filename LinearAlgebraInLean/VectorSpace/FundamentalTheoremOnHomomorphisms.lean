import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.LinearMap
import LinearAlgebraInLean.VectorSpace.Quotientspace
import LinearAlgebraInLean.VectorSpace.Kernel
import LinearAlgebraInLean.VectorSpace.Image
namespace LA

namespace LinearMap

variable  {F V} [F: Field F] [V: VectorSpace F V] [W: VectorSpace F W]
variable {U : Subspace V}

def InducedMap (Φ: LinearMap V W) : LinearMap (V / (Kernel.kernel Φ)) W := by

  let Φt : V / (Kernel.kernel Φ) -> W := Quotient.lift (fun x => Φ x) <| by
    -- some proof for a ≈ b → (fun x => Φ x) a = (fun x => Φ x) b
    intro a b hab
    simp
    --have : a - b ∈  Kernel.kernel Φ := by assumption

    simp[HasEquiv.Equiv, instHasEquivOfSetoid] at hab
    unfold Setoid.r QuotientSpace.rel at hab
    unfold QuotientSpace.relation at hab
    simp at hab
    apply Image.same_image_from_in_kernel
    assumption

  apply LinearMap.mk Φt
  intro v u μ
  induction v using Quotient.ind
  induction u using Quotient.ind
  rename_i v u

  let mk x : (V / (Kernel.kernel Φ)) := QuotientSpace.mk x

  exact calc
    Φt (μ • mk v + mk u)
    _ = Φ (μ • v + u) := by rfl
    _ = μ • Φ v + Φ u := by simp
    _ = μ • (Φt (mk v)) + Φt (mk u) := by rfl

theorem inducedMapIsInjective (Φ: LinearMap V W) :
    Function.Injective (InducedMap Φ) := by
  unfold Function.Injective
  intro a b h
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i a b

  let mk x : (V / (Kernel.kernel Φ)) := QuotientSpace.mk x
  have : Φ a = Φ b := by calc
    Φ a
    _ = (InducedMap Φ).hom (mk a) := by rfl
    _ = (InducedMap Φ).hom (mk b) := by exact h
    _ = Φ b := by rfl

  have : a - b ∈ Kernel.kernel Φ := Image.in_kernel_from_same_image this

  apply Quotient.sound
  have : QuotientSpace.relation V (Kernel.kernel Φ) a b := by assumption
  assumption

theorem originalIsInduedAndProjection (φ: LinearMap V W) : φ = (InducedMap φ) ∘ QuotientSpace.π := by
  apply LinearMap.ext
  intro x
  simp [chain, Function.comp]
  rfl

theorem inducedMapIsSurjective {Φ: LinearMap V W} (h: Function.Surjective Φ) : Function.Surjective (InducedMap Φ) := by
  unfold Function.Surjective x
  intro b
  have ⟨a,ha⟩ := h b
  exists QuotientSpace.π a
