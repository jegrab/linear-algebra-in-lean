import LinearAlgebraInLean.Infix
import LinearAlgebraInLean.Util

abbrev neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

abbrev operation (G: Type u): Type u:= G -> G -> G

class Operation (G: Type u) where
  op:  operation G

infixl:65 " ◾ " => Operation.op
notation "𝟙" => Inhabited.default



class Group (G: Type u) extends Operation G, Inv G, Inhabited G where
  assoc : ∀ a b c : G , (a ◾ b) ◾ c = a ◾  (b ◾ c)
  neutral_right : ∀ a : G , a ◾ 𝟙 = a
  neutral_left : ∀ a: G , 𝟙 ◾ a = a
  inverse_law_right : ∀ a : G, a ◾  a⁻¹ = 𝟙
  inverse_law_left : ∀ a : G, a⁻¹ ◾  a = 𝟙

attribute [simp] Group.assoc Group.neutral_right Group.neutral_left Group.inverse_law_left Group.inverse_law_right


instance: CoeSort (Group G) (Type) where
  coe _ := G
-- def Group.unique_neutral {a: G} [Group G] (ha : neutral_pred Operation.op a ) : a = neutral := unique_neutral ha Group.neutral_law
abbrev Group.neutral (G: Group G): G := G.default
theorem Group.inv_unique [G: Group G] (a: G): unique (fun x => x ◾ a = 𝟙) := by
  unfold unique
  simp
  intro a₁ a₂ h₁ h₂
  have := calc a⁻¹
    _ = 𝟙 ◾ a⁻¹ := by simp
    _ = a₁ ◾ a ◾ a⁻¹ := by simp [h₁]
    _ = a₁ := by simp
  have := calc a⁻¹
    _ = 𝟙 ◾ a⁻¹ := by simp
    _ = a₂ ◾ a ◾ a⁻¹ := by simp [h₂]
    _ = a₂ := by simp
  simp_all

@[simp] theorem Group.inv_inv [G: Group G]: ∀ a: G, a⁻¹⁻¹ = a := by
  intro a
  have : a ◾ a⁻¹ = 𝟙 := by simp
  have := Group.inv_unique (a⁻¹) a⁻¹⁻¹ a
  simp_all

abbrev Group.nonzeros (g : Group G):= {x : G // x ≠ 𝟙}


class AbelianGroup (G: Type) extends (Group G) where
  commutative_law : ∀ a b : G, a ◾ b = b ◾ a

attribute [simp] AbelianGroup.commutative_law

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

theorem Group.mulWithInversesRight [g: Group G] {a b : g}  : ∃! x : G, a ◾ x = b := by
  unfold existsUnique
  exists a⁻¹ ◾ b
  simp
  apply And.intro
  have := g.inverse_law_right
  simp [<-g.assoc, g.inverse_law_right, g.neutral_left]
  intro c hc
  simp [<-hc, <-g.assoc, g.inverse_law_left, g.neutral_left]


theorem mulWithInversesLeft (g: Group G) {a b : G}  : ∃! x : G, x ◾ a = b := by
  unfold existsUnique
  exists b ◾ a⁻¹
  simp
  intro y h
  have h := congrArg (. ◾ a⁻¹) h
  simp at h
  simp_all


instance SubGroup [G: Group G] (prop: G -> Prop) (h: prop G.neutral) (closed: ∀ a b : G, prop (a ◾ b⁻¹)):
Group (Subtype prop) where
  inv := by
    intro ⟨a, ha⟩
    exists a⁻¹
    have := closed G.neutral a
    simp [G.neutral_left] at this
    assumption

  op := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    exists a ◾ b
    have := closed a b⁻¹
    simp_all

  assoc := by
    simp

  default := ⟨𝟙, h⟩

  neutral_left := by simp
  neutral_right := by simp
  inverse_law_left := by simp
  inverse_law_right := by simp

instance AbelianSubGroup [G: AbelianGroup G] (prop: G -> Prop) (h: prop G.neutral) (closed: ∀ a b : G, prop (a ◾ b⁻¹)):
AbelianGroup (Subtype prop) := {
  toGroup := SubGroup prop h closed
  commutative_law := by simp [Operation.op]
}











#check {x // x > 0}
