import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.LinearMap
namespace LA


class Subspace (V: VectorSpace F V) where
  criterion ::
  pred: V -> Prop
  toVectorSpace: VectorSpace F (Subtype pred)
  add_is_add: ∀ x y: Subtype pred, (↑(x + y): V) = ↑x + ↑y
  smul_is_smul: ∀ (μ : F) (v: Subtype pred), (↑(μ • v): V) = μ • ↑v

attribute[simp] Subspace.add_is_add
attribute[reducible, instance] Subspace.toVectorSpace

-- instance [V: VectorSpace F V] (s: Subspace V): CoeDep (Subspace V) s (VectorSpace F $ Subtype s.pred) where
--   coe := s.toVectorSpace


instance : CoeSort (Subspace V) Type where
  coe x := Subtype x.pred

namespace Subspace
variable  {F V} [F: Field F] [V: VectorSpace F V] {pred: V -> Prop} [U: Subspace V]

#check U.toVectorSpace.zero

@[reducible] def mk (pred: V -> Prop)
  (inh: Inhabited $ Subtype pred)
  (closed: ∀ (u v: Subtype pred) (μ: F), pred $ μ • u + v)
  : Subspace V :=
  let subgroup := AbelianSubGroup pred inh <| by
    intro a b
    have := closed b a (-1)
    simp [AbelianGroup.comm, VectorSpace.smul_minus_left] at this
    apply this
  let smul μ v := by
      exists μ • v
      have h := closed v 0 μ
      simp [OfNat.ofNat, Zero.zero, subgroup] at h
      have : V.zero = (0: V) := by unfold OfNat.ofNat; unfold Zero.toOfNat0; simp
      rw [this] at h
      simp at h
      assumption
  {
    pred := pred
    toVectorSpace := {
      toAbelianGroup := subgroup
      smul := smul
      one_mul  := by
        intro ⟨v, hv⟩
        simp [HSMul.hSMul, smul]
        apply V.one_mul
      s_assoc := by
        intro μ γ ⟨c, hc⟩
        simp [HSMul.hSMul, smul]
        apply V.s_assoc
      s_distr_left := by
        intro μ γ ⟨v ,hv⟩
        simp [HSMul.hSMul, smul, HAdd.hAdd, subgroup, Add.add]
        apply V.s_distr_left
      s_distr_right := by
        intro μ ⟨u, hu⟩ ⟨v ,hv⟩
        simp [HSMul.hSMul, smul, HAdd.hAdd, subgroup, Add.add]
        apply V.s_distr_right
    }
    add_is_add := by simp [subgroup, HAdd.hAdd, Add.add]
    smul_is_smul := by simp [smul, HSMul.hSMul, SMul.smul]
  }


def embed (U: Subspace V): LinearMap U.toVectorSpace V :=
  let hom x := ↑x
  {
    hom := hom
    add := U.add_is_add
    scalar := U.smul_is_smul
  }

@[reducible] def zero_subspace: Subspace V := by
  apply Subspace.mk (. = (0: V))
  . apply Inhabited.mk
    exists 0
  . intro ⟨u, hu⟩ ⟨v, hv⟩ μ
    simp [hu, hv]

def zero_in_subspace (U: Subspace V): U.pred 0 := by
  have h := (0: U).property
  have : (0: U) = (0: V) := by
    rw [<-U.embed.zero]
    unfold embed
    simp
  rw [this] at h
  assumption






@[reducible] def intersect (U S: Subspace V) : Subspace V := by
  apply Subspace.mk (fun x => U.pred x ∧ S.pred x)
  . apply Inhabited.mk
    exists 0
    constructor <;> apply zero_in_subspace
    all_goals assumption
  . intro ⟨u, hu⟩ ⟨v, hv⟩ μ
    constructor
    have := (μ • (⟨u, hu.1⟩: U) + ⟨v, hv.1⟩).property
    have hom : ∀x, U.embed.hom x = ↑x := by simp [Subspace.embed]
    rw [<-hom, U.embed.add, U.embed.scalar] at this
    assumption
    have := (μ • (⟨u, hu.2⟩: S) + ⟨v, hv.2⟩).property
    have hom : ∀x, S.embed.hom x = ↑x := by simp [Subspace.embed]
    rw [<-hom, S.embed.add, S.embed.scalar] at this
    assumption

instance : Inter $ Subspace V where
  inter := intersect

@[reducible] def sum (U S: Subspace V) : Subspace V := by
  apply Subspace.mk (fun x => ∃u: V, U.pred u ∧ S.pred (x - u))
  . apply Inhabited.mk
    exists 0
    exists 0
    constructor <;> (try simp) <;> apply zero_in_subspace
  . intro ⟨u, hu⟩ ⟨v, hv⟩ μ
    obtain ⟨u₁, hu₁⟩ := hu
    obtain ⟨v₁, hv₁⟩ := hv
    exists μ • u₁ + v₁
    constructor
    . let := (μ • (⟨u₁, hu₁.left⟩: U) + ⟨v₁, hv₁.left⟩).property
      simp [U.add_is_add, U.smul_is_smul] at this
      rw [AbelianGroup.comm] at this
      apply this
    . simp
      let := ((⟨v - v₁, hv₁.right⟩ : S) + μ • ⟨u - u₁, hu₁.right⟩).property
      simp [S.smul_is_smul, S.add_is_add] at this
      conv => rhs; tactic => ac_nf
      conv at this => rhs; tactic => ac_nf
      assumption

instance : Add $ Subspace V where
  add := sum
