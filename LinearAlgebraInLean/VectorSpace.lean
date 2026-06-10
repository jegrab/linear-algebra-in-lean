import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field
import LinearAlgebraInLean.Sum

class VectorSpace (F: Field F) (V : Type) extends AbelianGroup V, SMul F V where
  one_mul : ∀ v: V, (1:F) • v = v
  s_assoc : ∀ (r s: F) (v : V), r • (s • v) = (r * s) • v
  s_distr_left : ∀ (r s : F) (v : V), (r+s)•v = (r•v) + (s•v)
  s_distr_right : ∀ (r: F) (v w : V), r•(v+w) = (r•v) + (r•w)

attribute[simp] VectorSpace.one_mul VectorSpace.s_assoc VectorSpace.s_distr_left VectorSpace.s_distr_right

instance : CoeSort (VectorSpace K V) Type where
  coe _ := V


namespace VectorSpace
variable [F: Field F] [V: VectorSpace F V]

@[simp] theorem smul_zero_right  (r : F) : r • (0: V) = 0 := by
  have h : r • (0 + (0:V)) = r • 0 + r • 0 := by rw [<-s_distr_right]
  have h : r • (0:V) = r • 0 + r • 0 := by simp [<-h]
  apply (Group.neutral_unique h.symm)

@[simp] theorem smul_zero_left (v : V) : (0:F) • v = 0 := by
  have := calc v
          _ = (1 + 0: F) • v := by simp
          _ = (1:F) • v + (0:F) • v := by rw [s_distr_left]
          _ = v + (0:F) • v := by simp
  apply Group.neutral_unique this.symm

@[simp] theorem smul_minus (x: F) (v : V) : (-x • v) = - (x•v) := by
  have : (0:F)•v = 0 := by simp
  have : (-x + x)•v = 0 := by simp
  have : -x • v + x • v = 0 := by rw[<-s_distr_left, this]
  apply Group.neg_unique_left this

@[simp] theorem zero_div_free (r : F) (v : V) (h: r • v = 0) : r = 0 ∨ v = 0 := by
  by_cases hr: r = 0
  . left
    assumption
  . right
    have h₂ : v = (1:F) • v := by simp
    let rn: F.non_zeros := ⟨r,hr⟩
    have : rn⁻¹.val * rn = 1 := by rw [Field.mul_inverse_left]
    rw [<-this] at h₂
    rw [<-s_assoc] at h₂
    rw [h] at h₂
    rw [smul_zero_right] at h₂
    exact h₂

@[simp] theorem sum_distr {is: List α} {v: α -> V} {x: F} : sum is (fun i => x • v i) = x • sum is v := by
  induction is with
  | nil =>
    unfold sum
    simp
  | cons i iss ih =>
    unfold sum
    simp[ih]


def linear_independent (F: Field F) (V: VectorSpace F V) (is: List α) (vs: α -> V) : Prop := ∀ (ls: α -> F), sum is (fun i => ls i • vs i) = 0 -> ∀ i ∈ is, ls i = 0

theorem v_is_lincomb_of_others_from_lin_dep [BEq α][LawfulBEq α]
        (is: List α) (vs: α -> V) (hl : ¬ linear_independent F V is vs) :
        ∃ i ∈ is, ∃ (ys: α -> F), vs i = sum (is.erase i) (fun j => ys j • vs j) := by
  unfold linear_independent at hl
  simp at hl
  have ⟨xs, h1, i1, h2,h3⟩ := hl
  exists i1
  constructor
  assumption
  let x1 : F.non_zeros := ⟨xs i1, by assumption⟩
  let ys i := -x1⁻¹.val * xs i
  exists ys
  have h := calc sum (is.erase i1) fun j => ys j • vs j
    _ = sum (is.erase i1) fun j => (-x1⁻¹.val * xs j) • vs j := by simp[ys]
    _ = sum (is.erase i1) fun j => -x1⁻¹.val • xs j • vs j := by simp
    _ = -x1⁻¹.val • sum (is.erase i1) fun j => xs j • vs j := by rw[sum_distr]
    _ =-(x1⁻¹.val • sum (is.erase i1) fun j => xs j • vs j) := by rw [smul_minus]
  rw [h]
  apply Group.neg_unique
  have h_one : x1⁻¹.val * x1.val = 1 := by
    have ⟨a,ha ⟩:=x1
    simp
  have h := calc
      vs i1
      _ = (1:F) • vs i1 := by simp
      _ = (x1⁻¹.val * x1.val) • vs i1 := by rw[h_one]
      _ = x1⁻¹.val • x1.val • vs i1 := by simp
      _ = x1⁻¹.val • sum [i1] (fun j => xs j • vs j) := by
        unfold sum
        unfold sum
        unfold x1
        simp
  rw [h]
  rw [<-s_distr_right]
  rw [Sum.split]
  rw [Sum.erase_then_add]
  . rw [h1]
    simp
  . rw [List.contains_eq_mem]
    simpa using h2

@[reducible] def SubSpace (pred: V -> Prop)
  (inh: Inhabited $ Subtype pred)
  (closed: ∀ (u v: Subtype pred) (μ: F), pred $ μ • u + v)
  : VectorSpace F (Subtype pred) :=
  let subgroup := AbelianSubGroup pred inh <| by
    intro a b
    have := closed b a (-1)
    simp [AbelianGroup.comm, smul_minus] at this
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


@[reducible] def zero_subspace: VectorSpace F $ Subtype $ (. = (0: V)) := by
  apply SubSpace
  . apply Inhabited.mk
    exists 0
  . intro ⟨u, hu⟩ ⟨v, hv⟩ μ
    simp [hu, hv]




end VectorSpace
