import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Subspace
import LinearAlgebraInLean.VectorSpace.SubspaceLemmas
namespace LA

namespace QuotientSpace

def relation (V: VectorSpace F V) (U : Subspace V) (u v : V) : Prop := u - v ∈ U

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


def rel (V: VectorSpace F V) (U : Subspace V) : Setoid V := Setoid.mk (relation V U) relation_is_eqrel

end QuotientSpace

abbrev QuotientSpaceType (V: VectorSpace F V) (U : Subspace V) : Type := Quotient (QuotientSpace.rel V U)



namespace QuotientSpace

def mk {V: VectorSpace F V} {U : Subspace V} : V -> QuotientSpaceType V U := Quotient.mk (rel V U)


instance QuotientSpace (V: VectorSpace F V) (U : Subspace V) : VectorSpace F (QuotientSpaceType V U) :=
  let smul(μ: F) : QuotientSpaceType V U ->  QuotientSpaceType V U := Quotient.lift (fun x => mk (μ • x)) <| by
    intro a b hab
    simp
    unfold mk
    apply Quotient.sound
    simp[HasEquiv.Equiv, instHasEquivOfSetoid] at hab
    unfold Setoid.r rel at hab
    unfold relation at hab
    simp at hab
    simp[HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r rel
    unfold relation
    simp
    rw [<-VectorSpace.smul_minus_right]
    rw [<-VectorSpace.s_distr_right]
    exact Subspace.closed_smul μ hab
  let qadd : QuotientSpaceType V U -> QuotientSpaceType V U -> QuotientSpaceType V U := Quotient.lift₂ (fun u v => mk (u + v)) <| by
    intro a1 b1 a2 b2 ha hb
    simp
    unfold mk
    apply Quotient.sound
    simp[HasEquiv.Equiv, instHasEquivOfSetoid] at ha
    simp[HasEquiv.Equiv, instHasEquivOfSetoid] at hb
    unfold Setoid.r rel at ha
    unfold Setoid.r rel at hb
    unfold relation at ha
    unfold relation at hb
    simp at ha
    simp at hb
    simp[HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r rel
    unfold relation
    simp
    rw [<-Group.assoc b1]
    rw [AbelianGroup.comm b1]
    rw [Group.assoc]
    rw [<-Group.assoc]
    apply Subspace.closed_add
    assumption
    assumption
  let neg : QuotientSpaceType V U -> QuotientSpaceType V U := Quotient.lift (fun u => mk (-u)) <| by
    intro a b hab
    simp
    unfold mk
    apply Quotient.sound
    simp[HasEquiv.Equiv, instHasEquivOfSetoid] at hab
    unfold Setoid.r rel at hab
    unfold relation at hab
    simp at hab
    simp[HasEquiv.Equiv, instHasEquivOfSetoid]
    unfold Setoid.r rel
    unfold relation
    simp
    let z := Subspace.closed (-1) hab (Subspace.zero_in_subspace U)
    simp at z
    assumption
  {
    add := qadd
    smul := smul
    zero := mk 0
    neg := neg
    assoc := by
      unfold_quotient
      apply Quotient.sound
      rw [V.assoc]
      apply relation_is_eqrel.refl
    neutral_right := by
      unfold_quotient
      apply Quotient.sound
      rw [V.neutral_right]
      apply relation_is_eqrel.refl
    neutral_left := by
      unfold_quotient
      apply Quotient.sound
      rw [V.neutral_left]
      apply relation_is_eqrel.refl
    inverse_left := by
      unfold_quotient
      apply Quotient.sound
      rw [V.inverse_left]
      apply relation_is_eqrel.refl
    inverse_right := by
      unfold_quotient
      apply Quotient.sound
      rw [V.inverse_right]
      apply relation_is_eqrel.refl
    comm := by
      unfold_quotient
      apply Quotient.sound
      rw [V.comm]
      apply relation_is_eqrel.refl
    one_mul := by
      unfold_quotient
      apply Quotient.sound
      rw [V.one_mul]
      apply relation_is_eqrel.refl
    s_assoc := by
      intro r s
      unfold_quotient
      apply Quotient.sound
      rw [V.s_assoc]
      apply relation_is_eqrel.refl
    s_distr_left := by
      intro r s
      unfold_quotient
      apply Quotient.sound
      rw [V.s_distr_left]
      apply relation_is_eqrel.refl
    s_distr_right := by
      intro r
      unfold_quotient
      apply Quotient.sound
      rw [V.s_distr_right]
      apply relation_is_eqrel.refl
  }

infixl:60 " / " => QuotientSpace

def π {V: VectorSpace F V} {U : Subspace V} : LinearMap.Hom V (V / U) := LinearMap.mk (Quotient.mk (rel V U)) <| by
  intro v u μ
  rfl

end QuotientSpace
