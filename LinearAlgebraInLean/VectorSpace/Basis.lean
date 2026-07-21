import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.Sum
import LinearAlgebraInLean.VectorSpace.Subspace
namespace LA.VectorSpace

open VectorSpace

variable [F: Field F] [V: VectorSpace F V]

abbrev Span (F: Field F) [V: VectorSpace F V] (vs: List V): Subspace V := by
  apply Subspace.mk (fun v: V => ∃ s: List F, s.length = vs.length ∧ v = sum (s.zipWith (. • .) vs))
  . constructor
    exists 0
    exists List.replicate vs.length 0
    constructor
    simp
    rw [<-List.map_const', List.zipWith_map_left, List.zipWith_self]
    simp
    rw [List.map_const', Sum.const_vs]
    simp
  . intro ⟨x, sx, lx, hx⟩ ⟨y, sy, ly, hy⟩ μ
    simp
    exists List.map (fun (x,y) =>  μ * x + y) $ sx.zip sy
    constructor
    . simp[lx, ly]
    simp[<-List.map_uncurry_zip_eq_zipWith]
    rw [List.zip_map_left, List.map_map]
    unfold Function.comp
    unfold Function.uncurry
    simp
    rw [Sum.unzip]
    congr
    . conv => rhs; rhs; lhs; (tactic => calc _ = Function.uncurry V.smul ∘ (Prod.map Prod.snd id) := by simp [Function.comp_def]; simp [Prod.map, <-SMul.smul_eq_hSMul])
      rw [<-List.map_map, <-List.zip_map, List.map_id, List.map_snd_zip, List.map_uncurry_zip_eq_zipWith]
      rwa [SMul.smul_eq_hSMul]
      apply Nat.le_of_eq
      simp [lx, ly]
    . conv => rhs; rhs; lhs; ext; rw [<-VectorSpace.s_assoc]
      conv => rhs; rhs; lhs; (tactic => rename_i x; calc _ = (μ • .) ∘ Function.uncurry SMul.smul ∘ Prod.map Prod.fst id := by unfold Function.uncurry; unfold Prod.map; unfold Function.comp; simp[SMul.smul_eq_hSMul] )
      rw [<-List.map_map, Sum.scalar]
      congr
      rw [<-List.map_map, <-List.zip_map, List.map_id, List.map_fst_zip, List.map_uncurry_zip_eq_zipWith]
      rwa [SMul.smul_eq_hSMul]
      apply Nat.le_of_eq
      simp [lx, ly]


def Basis (V: VectorSpace F V) (vs: List V) := Span F vs = V ∧ VectorSpace.linear_independent F vs

def linear_combination (F: Field F) [V: VectorSpace F V] (v: V) (vs: List V): Prop := ∃ (μs: List F) (_: μs.length = vs.length), v = sum (List.zipWith (. • .) μs vs)

theorem Basis.is_linear_combination (hb: Basis V bs) (v: V): linear_combination F v bs := by
  unfold linear_combination
  unfold Basis at hb
  have hspan := hb.left
  simp [Span] at hspan
  have hspan := hspan.left
  rw [funext_iff] at hspan
  simp at hspan
  have ⟨μ, hlen, hm⟩ := hspan v
  exists μ, hlen

theorem linear_independent.combination_dependent {n: Nat} (vs xs: List V) {hvlen : vs.length = n} {hxlen: xs.length = n + 1}
  (h: ∀ x ∈ xs, linear_combination F x vs)
  : ¬ VectorSpace.linear_independent F xs := by
  induction n generalizing xs vs with
  | zero =>
    simp_all
    cases xs with
      | nil => contradiction
      | cons x xs =>
        simp_all
        unfold linear_combination at h
        simp_all
        apply VectorSpace.zero_lin_dep
        simp
  | succ n hn =>
  cases vs with
  | nil => contradiction
  | cons v vs =>
  cases xs with
  | nil => contradiction
  | cons x xs =>
  simp_all
  have ⟨hv, h⟩ := h

  sorry

theorem append_lin_dep (vs xs: List V) (h: ¬ VectorSpace.linear_independent F vs)
  : ¬ VectorSpace.linear_independent F (vs ++ xs) := by
  unfold VectorSpace.linear_independent at *
  simp at *
  obtain ⟨μs, h_len, h_sum_zero, x_nz, hx_μ, hxnz⟩ := h
  exists μs ++ List.replicate xs.length 0
  constructor
  simp [h_len]
  constructor
  . rw [List.zipWith_append, <-Sum.split, h_sum_zero, List.zipWith_replicate_left]
    simp [List.map_const', Sum.const_vs]
    rfl
    assumption
  exists x_nz
  constructor
  simp [hx_μ]
  assumption

theorem Basis.equal_size: ∀ (b1 b2: List V) (_: Basis V b1) (_: Basis V b2), b1.length = b2.length := by
  suffices ∀ (b1 b2: List V) (hb1: Basis V b1) (hb2: Basis V b2), b1.length <= b2.length by
    intros
    apply Nat.eq_iff_le_and_ge.mpr
    constructor <;> apply this <;> assumption
  intro b1 b2 hb1 hb2
  unfold Basis at *
  false_or_by_contra
  rename_i hlt
  simp at hlt
  suffices ¬ VectorSpace.linear_independent F b1 from this hb1.right
  let b1' := b1.splitAt (b2.length + 1)
  have b1_len : b1'.1.length = b2.length + 1 := by
    unfold b1'
    simp [List.splitAt_eq, Nat.min_eq_left (Nat.succ_le_of_lt hlt)]
  have : b1 = b1'.1 ++ b1'.2 := by simp [b1']
  rw [this]
  apply append_lin_dep
  apply linear_independent.combination_dependent b2 b1'.fst
  intros
  apply Basis.is_linear_combination
  assumption
  apply b2.length
  rfl
  assumption



theorem exists_list {xs: List α} (h: ∀ x ∈ xs, ∃y: β, x = f y ) : ∃ ys: List β, xs = List.map f ys := by

  sorry

theorem exists_pair {p: (a: α) -> β a -> Prop }: (∃ (a: α) (b: β a), p a b) = ∃ (pair: PSigma β), p pair.1 pair.2 := by
    ext
    constructor
    . intro ⟨a, b, c⟩
      exact ⟨⟨a,b⟩, c⟩
    . intro ⟨⟨a,b⟩,c⟩
      exact ⟨a,b,c⟩

theorem combinations (bs: List V) (vs: List V)
  (h: ∀ v ∈ vs, ∃s : List F, linear_combination F v bs) (h_end: linear_combination F x vs)
  : linear_combination F x bs := by

  unfold linear_combination at *

  have ⟨μ_e, h_len, x_e⟩ := h_end
  conv at h => ext; ext; rw [exists_pair];  rw [exists_pair]

  have ⟨ls,eq⟩ := exists_list h
  rw [eq] at h_end
  conv at h_end => rhs; ext; rhs; ext; rhs; rw [List.zipWith_map_right]; rhs; arg 1;ext _ _; rw[ <-Sum.scalar]
  conv at h_end => rhs; ext; rhs; ext; rhs; rw [<-List.map_uncurry_zip_eq_zipWith]; unfold Function.uncurry; simp; rhs; lhs; ext; rw[<-List.map_uncurry_zip_eq_zipWith]; unfold Function.uncurry; simp
  -- conv at h_end => rhs; ext; rhs; ext; rhs; rw [Sum.sum_swap]



  -- have vs := vs.attach.map (fun v: Subtype (. ∈ vs) => PLift.up $ PSigma.mk v (h v v.property))

  sorry
