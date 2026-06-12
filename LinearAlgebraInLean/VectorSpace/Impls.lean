import LinearAlgebraInLean.VectorSpace.Def


instance FieldSpace: VectorSpace F F where
  toAbelianGroup := F.toAbelianGroup
  smul := (. * .)

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
