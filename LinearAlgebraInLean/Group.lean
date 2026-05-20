import LinearAlgebraInLean.Infix

abbrev neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

abbrev operation (G: Type): Type:= G -> G -> G

class Operation (G: Type) where
  op:  operation G

infixl:65 " ◾ " => Operation.op
notation "𝟙" => Inhabited.default



class Group (G: Type) extends Operation G, Inv G, Inhabited G where
assoc : ∀ a b c : G , (a ◾ b) ◾ c = a ◾  (b ◾ c)

neutral_left : ∀ a: G , 𝟙 ◾ a = a
neutral_right : ∀ a : G , a ◾ 𝟙 = a
-- neutral_law: neutral_pred Operation.op (𝟙: G) := (fun a => ⟨neutral_right a, neutral_left a⟩)
inverse_law_left : ∀ a : G, a ◾  a⁻¹ = 𝟙
inverse_law_right : ∀ a : G, a⁻¹ ◾  a = 𝟙

-- def Group.unique_neutral {a: G} [Group G] (ha : neutral_pred Operation.op a ) : a = neutral := unique_neutral ha Group.neutral_law


instance: CoeSort (Group G) (Type) where
  coe _ := G


abbrev Group.nonzeros (g : Group G):= {x : G // x ≠ 𝟙}


class AbelianGroup (G: Type) extends (Group G) where
  commutative_law : ∀ a b : G, a ◾ b = b ◾ a

instance : CoeSort (AbelianGroup G) (Type) where
  coe _ := G

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

set_option trace.Meta.synthInstance true
theorem Group.mulWithInversesRight [g: Group G] {a b : g}  : ∃! x : G, a ◾ x = b := by
  unfold existsUnique
  exists a⁻¹ ◾ b
  simp
  apply And.intro
  have := g.inverse_law_left
  simp [<-g.assoc, g.inverse_law_left, g.neutral_left]
  intro c hc
  simp [<-hc, <-g.assoc, g.inverse_law_right, g.neutral_left]


theorem mulWithInversesLeft (g: Group G) {a b : G}  : ∃! x : G, x ◾ a = b := by
  unfold existsUnique
  exists b ◾ a⁻¹
  simp
  apply And.intro
  simp [g.assoc, g.inverse_law_right, g.neutral_right]
  intro c hc
  simp [<-hc, g.assoc, g.inverse_law_left, g.neutral_right]
