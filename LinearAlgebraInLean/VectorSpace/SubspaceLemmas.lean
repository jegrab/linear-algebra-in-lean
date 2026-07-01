import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.LinearMap
import LinearAlgebraInLean.VectorSpace.Subspace
namespace LA
namespace Subspace
variable  {F V} [F: Field F] [V: VectorSpace F V] {pred: V -> Prop} {U: Subspace V}

def embed (U: Subspace V): LinearMap U.toVectorSpace V :=
  let hom x := ↑x
  {
    hom := hom
    add := U.add_is_add
    scalar := U.smul_is_smul
  }

theorem val_is_embed (U: Subspace V) (a: U): a.val = U.embed a := by
  unfold embed
  simp

def zero_in_subspace (U: Subspace V): 0 ∈ U := by
  have h := (0: U).property
  have : (0: U) = (0: V) := by
    rw [<-U.embed.zero]
    unfold embed
    simp
  rw [this] at h
  assumption






@[reducible] def intersect (U S: Subspace V) : Subspace V := by
  apply Subspace.mk (fun x => U.pred x ∧ S.pred x)
  . constructor
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
  . constructor
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

theorem eq_zero_from_pred {U : Subspace V} (h: ∀x: V, U.pred x -> x = 0): U = zero_subspace := by
  ext
  constructor
  . simp
    apply h
  . simp
    intro hx
    rw[hx]
    exact zero_in_subspace U


theorem closed {U : Subspace V} {u v : V} (μ: F) (hu: u ∈ U) (hv: v ∈ U) : (μ • u + v∈ U) := by
  simp [Membership.mem] at hu
  simp [Membership.mem] at hv
  simp[Membership.mem]
  let u' := Subtype.mk u hu
  let v' := Subtype.mk v hv
  let r' := μ • u' + v'
  have a := r'.property
  unfold r' u' v' at a
  rw [Subspace.val_is_embed] at a
  simp at a
  rw [<-Subspace.val_is_embed] at a
  rw [<-Subspace.val_is_embed] at a
  simp at a
  exact a
