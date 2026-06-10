import LinearAlgebraInLean.VectorSpace.Def

namespace LA

structure LinearMap (V: VectorSpace F V) (W: VectorSpace F W) extends GroupHom V.toGroup W.toGroup where
  scalar: ∀ (μ: F) (v: V), hom (μ • v) = μ • hom v

namespace LinearMap
variable [V: VectorSpace F V] [W: VectorSpace F W]

attribute[simp] LinearMap.scalar


instance : CoeFun (LinearMap V W) (λ_ => (V -> W)) where
  coe hom := hom.hom

def simple (hom: V → W) (rule: ∀ (v u: V) (μ: F), hom (μ • v + u) = μ • hom v + hom u) : LinearMap V W :=
  let group := {
    hom := hom
    add a b := by
      have := rule a b 1
      simp at this
      assumption
  }
  {
    toGroupHom := group
    scalar μ v := by
      have := rule v 0 μ
      have h: hom = group.hom := by rfl
      simp [h, group.zero] at this
      assumption
  }
