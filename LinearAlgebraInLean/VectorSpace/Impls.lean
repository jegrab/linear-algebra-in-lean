import LinearAlgebraInLean.VectorSpace.Def
import LinearAlgebraInLean.VectorSpace.Basis

namespace LA.VectorSpace

instance FieldSpace (F: Field F): VectorSpace F F where
  toAbelianGroup := F.toAbelianGroup
  smul := (. * .)

theorem DefaultFieldBasis [F: Field F]: Basis (FieldSpace F) [1] := by
  unfold Basis
  constructor
  . ext x
    simp
    exists [x]
    constructor
    simp
    simp
    simp [HSMul.hSMul, SMul.smul]
  . unfold VectorSpace.linear_independent
    intro ls h_len sum_zero l l_in_ls
    unfold List.zipWith at sum_zero
    cases ls with
    | nil => contradiction
    | cons x xs =>
    simp_all
    simp [HSMul.hSMul, SMul.smul] at sum_zero
    assumption



instance TupleSpace (F: Field F) (n: Nat): VectorSpace F $ Vector F n where
  assoc a b c := by
    apply Vector.add_assoc
    ac_nf
    simp
  neutral_right a := by
    apply Vector.add_zero
    simp
  neutral_left a := by
    apply Vector.zero_add
    simp
  inverse_left := by
    apply Vector.neg_add_cancel
    simp
  inverse_right := by
    intro a
    have := Vector.add_comm F.comm a (-a)
    simp [this]
    apply Vector.neg_add_cancel
    simp
  comm := by
    apply Vector.add_comm
    simp
  s_distr_left := by
    apply Vector.add_smul
    simp
  s_distr_right := by
    apply Vector.smul_add
    simp
  s_assoc := by
    intros
    apply Eq.symm
    apply Vector.mul_smul
    simp
  one_mul v := by
    apply Vector.ext
    simp



theorem Sum.delta_vs [F: Field F] [G: VectorSpace F G] {f: α -> G} {ls: List α} {h: n = ls.length} (j: Nat)  {hj: j < n}
  : sum (List.zipWith (fun l (i: Fin n) => (δ i j :F) • f l) ls $ List.finRange n) = f ls[j] := by
  induction n generalizing ls j with
  | zero => contradiction
  | succ n ih =>
    cases ls with
    | nil => contradiction
    | cons l ls =>
    rw [List.finRange_succ, List.zipWith_cons_cons, List.zipWith_map_right]
    unfold sum
    unfold Fin.succ
    simp
    cases j with
    | zero =>
      unfold δ
      simp [<-List.map_uncurry_zip_eq_zipWith]
      unfold Function.uncurry
      simp [List.map_const', min, Sum.const_vs]
    | succ j' =>
      simp at h
      conv => lhs; lhs; unfold δ
      simp
      conv => pattern fun _ => _; ext a b; rw [<-delta.succ]
      rw [ih]
      simp at hj
      assumption
      assumption


theorem Sum.delta [G: Field G] {f: α -> G} {ls: List α} {h: n = ls.length} (j: Nat)  {hj: j < n}
  : sum (List.zipWith (fun l (i: Fin n) => δ i j * f l) ls $ List.finRange n) = f ls[j] := by
  let := FieldSpace G
  have {a b: G}: a * b = a • b := by simp[HSMul.hSMul, SMul.smul, this]
  conv => pattern fun _ => _; ext _ _; rw [this]
  apply Sum.delta_vs
  all_goals assumption


theorem DefaultBasis [F: Field F]: Basis (TupleSpace F n) $ List.map (fun x => (Vector.zero).set x.val 1) $ List.finRange n := by
  unfold Basis
  constructor
  . ext x
    simp
    exists x.toList
    constructor
    . simp
    rw [<-List.map_uncurry_zip_eq_zipWith, List.zip_map_right, List.map_map]
    unfold Function.comp
    unfold Function.uncurry
    simp
    simp [HSMul.hSMul, SMul.smul, Vector.smul, Vector.zero, Vector.map_replicate, Mul.mul_eq_hMul]
    rw [List.map_zip_eq_zipWith]
    unfold Function.curry
    simp
    ext i hi
    rw [Sum.vector_component, List.map_zipWith]
    conv => pattern (fun _ => _); ext x y; rw [Vector.getElem_set]; simp; tactic => (calc _ = δ y i * x := by unfold δ; split; all_goals simp)
    rw [Sum.delta]
    simp
    assumption
    simp
  . unfold VectorSpace.linear_independent
    intro ls h_len sum_zero l h_l_in_ls
    simp_all
    rw [List.zipWith_map_right] at sum_zero
    unfold Vector.zero at sum_zero
    simp [Vector.ext_iff] at sum_zero
    simp [Sum.vector_component, Vector.getElem_set] at sum_zero

    have {i} : (fun x (y: Fin n) => x • if (y: Nat) = i then 1 else 0) = (fun x (y: Fin n) => (δ (y) i: F) * x) := by
        unfold δ
        simp [HSMul.hSMul, SMul.smul]
        rw [Mul.mul_eq_hMul]

    conv at sum_zero => pattern fun _ => _; rw [this]
    conv at sum_zero => ext x h; lhs; rw [@Sum.delta F _ n (hj := h) (h := h_len.symm)]
    have ⟨i, hi, hh⟩ := List.getElem_of_mem h_l_in_ls
    rw [h_len] at hi
    rw [<-hh]
    apply sum_zero i hi
