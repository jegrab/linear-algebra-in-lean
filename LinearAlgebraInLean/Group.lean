namespace LinAlg

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

abbrev nonzeros (g : Group G op):= {x : G // x ≠ g.neutral}

structure AbelianGroup (G: Type) (op : operation G) extends (Group G op) where
  commutative_law : ∀ a b : G, op a b = op b a

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

end LinAlg
