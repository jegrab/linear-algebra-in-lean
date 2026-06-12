import LinearAlgebraInLean.VectorSpace.Def

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
  assoc := by
    intros
    funext
    dsimp [HAdd.hAdd]
    dsimp [Add.add_eq_hAdd]
    ac_nf
  neutral_left := by
    intros
    funext
    dsimp [HAdd.hAdd, OfNat.ofNat]
    dsimp [Add.add_eq_hAdd]
    simp [Zero.zero_is_ofNat]
  neutral_right := by
    intros
    funext
    dsimp [HAdd.hAdd, OfNat.ofNat]
    dsimp [Add.add_eq_hAdd]
    simp [Zero.zero_is_ofNat]
  inverse_left := by
    intros
    funext
    dsimp [HAdd.hAdd, OfNat.ofNat]
    simp [Add.add_eq_hAdd, Zero.zero_is_ofNat]
  inverse_right := by
    intros
    funext
    dsimp [HAdd.hAdd, OfNat.ofNat]
    simp [Add.add_eq_hAdd, Zero.zero_is_ofNat]
  comm := by
    intros
    funext
    dsimp [HAdd.hAdd, OfNat.ofNat]
    simp [Add.add_eq_hAdd]
  one_mul := by
    intros
    funext
    dsimp [HSMul.hSMul, OfNat.ofNat]
    simp [SMul.smul_eq_hSMul, One.one_is_ofNat]
  s_assoc := by
    intros
    funext
    dsimp [HSMul.hSMul]
    simp [SMul.smul_eq_hSMul]
  s_distr_left := by
    intros
    funext
    simp [HSMul.hSMul, HAdd.hAdd]
    simp [Add.add_eq_hAdd, SMul.smul_eq_hSMul]
  s_distr_right := by
    intros
    funext
    simp [HSMul.hSMul, HAdd.hAdd]
    simp [Add.add_eq_hAdd, SMul.smul_eq_hSMul]

instance: VectorSpace F $ LinearMap V W :=
  let := FunVectorSpace V W
  {
    add a b := by
      apply LinearMap.mk $ a.hom + b.hom
      intros
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd]
      ac_nf
    smul μ a := by
      apply LinearMap.mk $ μ • a.hom
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd]
    neg a := by
      apply LinearMap.mk $ fun x => - a x
      simp
    zero := by
      apply LinearMap.mk $ fun _ => 0
      simp
    assoc := by
      intros
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd]
    neutral_left := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat]
    neutral_right := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat]
    inverse_left := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat]
    inverse_right := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat]
    comm := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat]
    one_mul := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat]
    s_assoc := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat]

    s_distr_left := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat]
    s_distr_right := by
      intros
      apply ext
      dsimp [HAdd.hAdd, HSMul.hSMul, Add.add, this, SMul.smul, mk, OfNat.ofNat]
      simp [SMul.smul_eq_hSMul, Add.add_eq_hAdd, Zero.zero_is_ofNat, One.one_is_ofNat]

  }









infixl:60 (priority:= high) " ∘ " => LinearMap.chain

variable (X Y: LinearMap V V)
#check X ∘ Y
