import LinearAlgebraInLean.Infix

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

def existsUnique (p: T -> Prop) := ∃ x : T, (p x ∧ ∀ y : T, p y -> x = y)
open Lean.TSyntax.Compat in
macro "∃!" v:ident " : " t:term ", " b:term : term =>
  `(@existsUnique $t (fun $v => $b))

theorem mulWithInversesRight (g: Group G op) {a b : G}  : ∃! x : G, op a x = b :=
  by
  let x := op (g.neg a) b
  have h: op a x = b := by
    calc
      op a x = a §op§ ((g.neg a) §op§ b)  := by rfl
           _ = (a §op§ (g.neg a)) §op§ b  := by simp [g.assoc]
           _ = g.neutral §op§ b           := by simp [g.inverse_law_left]
           _ = b                          := by simp [g.neutral_left]
  have u : ∀ y : G, op a y = b -> x = y := by
    intro y
    intro h1
    have h2 : a §op§ x = a §op§ y                                   := by simp [h1,h]
    have h2 : (g.neg a) §op§ (a §op§ x) = (g.neg a) §op§ (a §op§ y) := by simp [h2]
    have h2 : ((g.neg a) §op§ a) §op§ x = ((g.neg a) §op§ a) §op§ y := by simp [h2, g.assoc]
    have h2 : g.neutral §op§ x = g.neutral §op§ y                   := by rw [<-g.inverse_law_right a, h2]
    have h2 : x = y                                                 := by rw [<-g.neutral_left x, <-g.neutral_left y, h2]
    exact h2
  exact ⟨x,⟨h,u⟩⟩
