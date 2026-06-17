import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Tactics

namespace LA

structure LinearMap (V: VectorSpace F V) (W: VectorSpace F W) extends GroupHom V.toGroup W.toGroup where
  from_def ::
  scalar: ∀ (μ: F) (v: V), hom (μ • v) = μ • hom v

namespace LinearMap
variable [F: Field F] [V: VectorSpace F V] [W: VectorSpace F W]

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

@[ext] theorem ext (φ ψ: LinearMap V W): (∀ x, φ x = ψ x) → φ = ψ := by
  intro h
  cases φ <;> cases ψ
  simp at *
  ext
  simp [h]



def chain (φ: LinearMap W X) (ψ: LinearMap V W): LinearMap V X := by
  apply mk (φ ∘ ψ)
  simp

infixl:90 (priority:= high) " ∘ " => LinearMap.chain

variable (X Y: LinearMap V V)
#check X ∘ Y

def id : LinearMap V V := by
  apply mk _root_.id
  simp

@[simp] theorem chain.assoc [A: VectorSpace F A] [B: VectorSpace F B] [C: VectorSpace F C] [D: VectorSpace F D]
  {φ: LinearMap C D} {ψ: LinearMap B C} {θ: LinearMap A B}
  :  φ ∘ (ψ ∘ θ) = (φ ∘ ψ) ∘ θ := by
    ext
    unfold chain
    simp

@[simp] theorem chain.id_left {φ: LinearMap V W} : id ∘ φ = φ := by
  ext
  simp [id, mk, chain]

@[simp] theorem chain.id_right {φ: LinearMap V W} : φ ∘ id = φ := by
  ext
  simp [id, mk, chain]




instance FunVectorSpace (X: Type) (V: VectorSpace F V): VectorSpace F $ X -> V where
  add a b x := a x + b x
  smul μ a x := μ • a x
  neg a x :=  - a x
  zero x :=  0

instance Hom (V: VectorSpace F V) (W: VectorSpace F W): VectorSpace F $ LinearMap V W :=
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
  }

abbrev Endo (V: VectorSpace F V) := Hom V V

structure Isomorphism (V: VectorSpace F V) (W: VectorSpace F W) where
  fwd : LinearMap V W
  back : LinearMap W V
  left : fwd ∘ back = id
  right : back ∘ fwd = id

instance : CoeFun (Isomorphism V W) (fun _ =>  V -> W) where
  coe φ := φ.fwd

def Isomorphism.invert (φ: Isomorphism V W): Isomorphism W V where
  back := φ.fwd
  fwd := φ.back
  left := φ.right
  right := φ.left

postfix:max (priority := high) "⁻¹" => Isomorphism.invert

def isomorphic (V: VectorSpace F V) (W: VectorSpace F W): Prop := Nonempty $ Isomorphism V W

infix:100 " ≅ " => isomorphic

@[refl] theorem isomorphic.refl: V ≅ V := by
  unfold isomorphic
  constructor
  constructor
  show id ∘ id = id; rfl
  show id ∘ id = id; rfl

@[symm] theorem isomorphic.symm: V ≅ W -> W ≅ V := by
  unfold isomorphic
  intro a
  cases a
  rename_i a
  constructor
  apply a.invert

theorem isomorphic.trans [Z: VectorSpace F Z]
  : V ≅ W -> W ≅ Z -> V ≅ Z := by
  unfold isomorphic
  intro a b
  cases a; rename_i a
  cases b; rename_i b
  constructor
  constructor
  . show (b.fwd ∘ a.fwd) ∘ (a.back ∘ b.back) = id
    conv => lhs; rw [<-chain.assoc]; rhs; rw [chain.assoc]
    simp [a.left, b.left]
  . conv => lhs; rw [<-chain.assoc]; rhs; rw [chain.assoc]
    simp [a.right, b.right]

instance [F: Field F]: @Trans (VectorSpace F V) (VectorSpace F W) (VectorSpace F Z) isomorphic isomorphic isomorphic where
  trans := isomorphic.trans
