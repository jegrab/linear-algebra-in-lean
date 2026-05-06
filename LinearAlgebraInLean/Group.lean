def neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

def operation (G: Type) := G -> G -> G

structure Group (G: Type) (op : operation G) where
  neg : G -> G
  neutral : G
  type : Type := G
  assoc : ∀ a b c : G , op (op a b) c = op a (op b c)

  neutral_left : ∀ a , op neutral a = a := (fun a => (neutral_law a).right)
  neutral_right : ∀ a : G , op a neutral = a := (fun a => (neutral_law a).left)
  neutral_law: neutral_pred op neutral := (fun a => ⟨neutral_right a, neutral_left a⟩)
  inverse_law_left : ∀ a : G, op a (neg a) = neutral
  inverse_law_right : ∀ a : G, op (neg a) a = neutral

  unique_neutral (ha : neutral_pred op a) : a = neutral := unique_neutral ha neutral_law

  nonzeros:= {x : G // x ≠ neutral}

structure AbelianGroup (G: Type) (op : operation G) extends (Group G op) where
  commutative_law : ∀ a b : G, op a b = op b a

def IntGroup : AbelianGroup Int Int.add := {
  neg := Int.neg
  neutral := 0
  assoc := Int.add_assoc
  neutral_left := Int.zero_add
  neutral_right := Int.add_zero
  inverse_law_left := fun  a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    exact h
  inverse_law_right := fun a => by
    have h := Int.add_neg_cancel_left a 0
    simp at h
    rw [Int.add_comm] at h
    exact h
  commutative_law := Int.add_comm
}

instance RatAddGroup : AbelianGroup Rat Rat.add where
  neg := Rat.neg
  neutral := 0
  assoc := Rat.add_assoc
  neutral_left := Rat.zero_add
  neutral_right := Rat.add_zero
  inverse_law_left := Rat.add_neg_cancel
  inverse_law_right := fun a => by
    have h := Rat.add_neg_cancel a
    rw [Rat.add_comm] at h
    exact h
  commutative_law := Rat.add_comm

#check Rat.mul_eq_zero.mp

abbrev zero_devisor_free (op: operation S) (z) := ∀ a b :S,  a = z ∨ b = z ↔ op a b = z

def closed_nonzero {S: Type} {z: S} (op: operation S) (h: zero_devisor_free op z) : operation {x: S // x ≠ z} :=
  fun a b =>
    have hnz: op a b ≠ z := by
      simp [zero_devisor_free] at *
      have ha: a ≠ z := a.property
      have hb: b ≠ z := b.property
      have hab: ¬ (a = z ∨ b = z) := by
        intro a
        have := a.imp ha hb
        simp at *
      exact hab.imp ((h a b).mpr)
    ⟨op a b, hnz⟩

def x : ∀ a b : Rat,  a = 0 ∨ b = 0 ↔ a * b = 0 := fun a b => (@Rat.mul_eq_zero a b).symm

-- set_option pp.all true
def rat_mul_non_zero := closed_nonzero Rat.mul x

def nonzero_rat := { x : Rat // x ≠ 0}
instance : Mul nonzero_rat where
  mul := rat_mul_non_zero

theorem ret_non_zero_mul_is_mul (a b : Rat) (ha: a ≠ 0) (hb : b ≠ 0) : (⟨ a * b, (rat_mul_non_zero ⟨a, ha ⟩  ⟨b,hb⟩).property⟩: nonzero_rat)  = (rat_mul_non_zero ⟨a, ha⟩ ⟨b, hb⟩) := by
  simp [rat_mul_non_zero, closed_nonzero]
  rfl

theorem inv_not_zero (x : Rat) (h : x ≠ 0) : Rat.inv x ≠ 0 := by
  let r := Rat.inv x
  by_cases hx : x >= 0
  by_cases hx : x = 0
  contradiction
  have hx : x > 0 := by grind
  have hr : r > 0 := by
    apply Rat.inv_pos.mpr
    assumption
  have hr : r ≠ 0 := by
    intro heq
    have : (0: Rat) > 0 := by
      rw [heq] at hr
      assumption
    contradiction
  exact hr
  have hx : x < 0 := by grind
  have hr : r < 0 := by
    sorry
  have hr : r ≠ 0 := by
    intro heq
    have : (0: Rat) > 0 := by
      rw [heq] at hr
      assumption
    contradiction
  exact hr

def rat_inv_non_zero (x: nonzero_rat) : nonzero_rat := by
  let ⟨x, h⟩ := x
  let r := Rat.inv x
  exact ⟨r, inv_not_zero x h⟩

variable (a : Rat) (ha: a ≠ 0)
#check (rat_inv_non_zero ⟨a, ha ⟩).property

theorem rat_non_zero_inv_is_inv (a : Rat) (ha: a ≠ 0) : (⟨ Rat.inv a, inv_not_zero a ha ⟩: nonzero_rat)  = (rat_inv_non_zero ⟨a, ha⟩) := by
  simp [rat_inv_non_zero, inv_not_zero]

instance RatMulGroup : AbelianGroup { x : Rat // x ≠ 0} rat_mul_non_zero where
  neg := rat_inv_non_zero
  neutral := ⟨1, by simp⟩
  assoc := by
    intro ⟨a, ha⟩  ⟨ b, hb⟩  ⟨ c, hc⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.mul_assoc]
  neutral_left := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.one_mul]
  neutral_right := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, Rat.mul_one]
  inverse_law_left := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.mul_inv_cancel
    assumption
  inverse_law_right := by
    intro ⟨a, ha⟩
    simp [<-ret_non_zero_mul_is_mul, <-rat_non_zero_inv_is_inv]
    apply Rat.inv_mul_cancel
    assumption
  commutative_law := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [<-ret_non_zero_mul_is_mul]
    apply Rat.mul_comm

-- instance [ag: AbelianGroup Rat Rat.add] : AbelianGroup ag.nonzeros

example (G: Group G op) : op (G.neutral) (G.neutral) = G.neutral := by
  apply Group.neutral_left
