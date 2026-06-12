import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Tactics

namespace LA

structure LinearMap (V: VectorSpace F V) (W: VectorSpace F W) extends GroupHom V.toGroup W.toGroup where
  from_def ::
  scalar: ∀ (μ: F) (v: V), hom (μ • v) = μ • hom v

namespace LinearMap
variable [V: VectorSpace F V] [W: VectorSpace F W]

attribute[simp] LinearMap.scalar


instance : CoeFun (LinearMap V W) (λ_ => (V -> W)) where
  coe hom := hom.hom

abbrev mk (hom: V → W) (rule: ∀ (v u: V) (μ: F), hom (μ • v + u) = μ • hom v + hom u) : LinearMap V W :=
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

def ext (φ ψ: LinearMap V W): (∀ x, φ x = ψ x) → φ = ψ := by
  intro h
  cases φ <;> cases ψ
  simp at *
  apply GroupHom.ext
  simp [h]



def chain (φ: LinearMap W X) (ψ: LinearMap V W): LinearMap V X := by
  apply mk (φ ∘ ψ)
  simp



instance FunVectorSpace (X: Type) (Y: VectorSpace F Y): VectorSpace F $ X -> Y where
  add a b x := a x + b x
  smul μ a x := μ • a x
  neg a x :=  - a x
  zero x :=  0
  assoc := by vector_space_refold; intros; ac_nf
  neutral_left := by vector_space_refold
  neutral_right := by vector_space_refold
  inverse_left := by vector_space_refold
  inverse_right := by vector_space_refold
  comm := by vector_space_refold
  one_mul := by vector_space_refold
  s_assoc := by vector_space_refold
  s_distr_left := by vector_space_refold
  s_distr_right := by vector_space_refold

instance: VectorSpace F $ LinearMap V W :=
  let := FunVectorSpace V W
  {
    add a b := by
      apply LinearMap.mk $ a.hom + b.hom
      vector_space_refold [this]
      intros; ac_nf
    smul μ a := by
      apply LinearMap.mk $ μ • a.hom
      vector_space_refold [this]
    neg a := by
      apply LinearMap.mk $ - a.hom
      vector_space_refold [this]
    zero := by
      apply LinearMap.mk $ 0
      vector_space_refold [this]
    assoc := by vector_space_refold [this]
    neutral_left := by vector_space_refold [this]
    neutral_right := by vector_space_refold [this]
    inverse_left := by vector_space_refold [this]
    inverse_right :=by vector_space_refold [this]
    comm := by vector_space_refold [this]
    one_mul := by vector_space_refold [this]
    s_assoc := by vector_space_refold [this]
    s_distr_left := by vector_space_refold [this]
    s_distr_right := by vector_space_refold [this]
  }






infixl:60 (priority:= high) " ∘ " => LinearMap.chain

variable (X Y: LinearMap V V)
#check X ∘ Y
