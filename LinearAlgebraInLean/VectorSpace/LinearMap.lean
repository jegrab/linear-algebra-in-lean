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

def ext (φ ψ: LinearMap V W): (∀ x, φ x = ψ x) → φ = ψ := by
  intro h
  cases φ <;> cases ψ
  simp at *
  apply GroupHom.ext
  simp [h]



def chain (φ: LinearMap W X) (ψ: LinearMap V W): LinearMap V X := by
  apply LinearMap.simple (φ ∘ ψ)
  simp

instance: VectorSpace F $ LinearMap V W where
  add a b := by
    apply LinearMap.simple $ fun x => a x + b x
    intros
    simp
    ac_nf
  smul μ a := by
    apply LinearMap.simple $ fun x => μ • a x
    simp
  neg a := by
    apply LinearMap.simple $ fun x => - a x
    simp
  zero := by
    apply LinearMap.simple $ fun _ => 0
    simp
  assoc := by
    simp [HAdd.hAdd, simple]
    funext
    simp [Add.add_eq_hAdd]
  neutral_left := by
    intro
    apply ext
    simp [HAdd.hAdd,simple]
    unfold OfNat.ofNat
    unfold simple
    unfold Zero.toOfNat0
    simp
    rw [Zero.zero_is_zero]
    intros
    rw [Add.add_eq_hAdd]
    simp
  neutral_right := by
    intro
    apply ext
    simp [HAdd.hAdd,simple]
    unfold OfNat.ofNat
    unfold simple
    unfold Zero.toOfNat0
    simp
    rw [Zero.zero_is_zero]
    intros
    rw [Add.add_eq_hAdd]
    simp
  inverse_left := by
    intro
    apply ext
    simp [HAdd.hAdd,simple]
    unfold OfNat.ofNat
    unfold simple
    unfold Zero.toOfNat0
    simp
    rw [Zero.zero_is_zero]
    intros
    simp [Add.add_eq_hAdd]
  inverse_right := by
    intro
    apply ext
    simp [HAdd.hAdd,simple]
    unfold OfNat.ofNat
    unfold simple
    unfold Zero.toOfNat0
    simp
    rw [Zero.zero_is_zero]
    intros
    simp [Add.add_eq_hAdd]
  comm := by
    intros
    apply ext
    simp [HAdd.hAdd,simple]
    intro
    simp [Add.add_eq_hAdd]
  one_mul := by
    intros
    apply ext
    intro
    simp [HSMul.hSMul, simple]
    simp [SMul.smul_eq_hSMul]
  s_assoc := by
    intros
    apply ext
    intros
    simp [HSMul.hSMul, simple]
    simp [SMul.smul_eq_hSMul]
  s_distr_left := by
    intros
    apply ext
    intros
    simp [HSMul.hSMul, HAdd.hAdd, simple]
    simp [Add.add_eq_hAdd, SMul.smul_eq_hSMul]
  s_distr_right := by
    intros
    apply ext
    intros
    simp [HSMul.hSMul, HAdd.hAdd, simple]
    simp [Add.add_eq_hAdd, SMul.smul_eq_hSMul]






infixl:60 (priority:= high) " ∘ " => LinearMap.chain

variable (X Y: LinearMap V V)
#check X ∘ Y
