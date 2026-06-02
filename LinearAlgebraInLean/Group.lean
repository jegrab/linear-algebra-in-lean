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

class Neutral (G: Type u) where
  neutral: G

class GroupInv (G: Type u) where
  groupInv: G -> G

infixl:65 " ◾ " => Operation.op
notation "𝟙" => Neutral.neutral
postfix:max "⁻" => GroupInv.groupInv



class Group (G: Type u) extends Operation G, GroupInv G, Neutral G where
  assoc : ∀ a b c : G , (a ◾ b) ◾ c = a ◾  (b ◾ c)
  neutral_right : ∀ a : G , a ◾ 𝟙 = a
  neutral_left : ∀ a: G , 𝟙 ◾ a = a
  inverse_right : ∀ a : G, a ◾ a⁻ = 𝟙
  inverse_left : ∀ a : G, a⁻ ◾ a = 𝟙

attribute [simp] Group.assoc Group.neutral_right Group.neutral_left Group.inverse_left Group.inverse_right

instance: CoeSort (Group G) (Type) where
  coe _ := G

instance [g: Group G]: Std.Associative (α := G) Operation.op := ⟨g.assoc⟩

abbrev GroupFromRight [Operation G] [GroupInv G] [Neutral G]
(assoc: ∀ a b c : G , (a ◾ b) ◾ c = a ◾  (b ◾ c))
(neutral_right: ∀ a : G , a ◾ 𝟙 = a)
(inverse_right:  ∀ a : G, a ◾  a⁻ = 𝟙)
: Group G where
  assoc := assoc
  inverse_right := inverse_right
  neutral_right := neutral_right
  neutral_left := by
    intro a
    apply Eq.symm
    calc a
      _ = a ◾ 𝟙 := by rw [neutral_right]
      _ = a ◾ a⁻ ◾ a⁻⁻ := by rw [assoc, inverse_right]
      _ = 𝟙 ◾ a⁻⁻  := by rw [inverse_right]
      _ = 𝟙 ◾ a := by grind
  inverse_left := by
    intro a
    apply Eq.symm
    calc 𝟙
      _ = a⁻ ◾ a ◾ (a⁻ ◾ a)⁻ := by rw [inverse_right]
      _ = a⁻ ◾ a ◾ a⁻ ◾ a := by grind
      _ = a⁻ ◾ a := by conv => lhs; lhs; rw [assoc, inverse_right, neutral_right]


theorem Group.inv_unique [G: Group G] (a: G): unique (fun x => x ◾ a = 𝟙) := by
  unfold unique
  simp
  intro a₁ a₂ h₁ h₂
  have := calc a⁻
    _ = 𝟙 ◾ a⁻ := by simp
    _ = a₁ ◾ a ◾ a⁻ := by simp [h₁]
    _ = a₁ := by simp
  have := calc a⁻
    _ = 𝟙 ◾ a⁻ := by simp
    _ = a₂ ◾ a ◾ a⁻ := by simp [h₂]
    _ = a₂ := by simp
  simp_all

theorem Group.neutral_unique [G: Group G] : unique (fun x => ∀ a:G, x ◾ a = x) := by
  unfold unique
  simp
  intro b₁ b₂ h₁ h₂
  have := h₁ b₁⁻
  have := h₂ b₂⁻
  simp at *
  simp_all


@[simp] theorem Group.inv_inv [G: Group G]: ∀ a: G, a⁻⁻ = a := by
  intro a
  have : a ◾ a⁻ = 𝟙 := by simp
  have := Group.inv_unique (a⁻) a⁻⁻ a
  simp_all
@[simp] theorem Group.inv_neutral [G: Group G]: (𝟙: G)⁻ = 𝟙 := by
  have : (𝟙:G) ◾ 𝟙 = 𝟙 := by simp
  have := Group.inv_unique (𝟙: G) 𝟙 𝟙⁻ this (Group.inverse_left _)
  apply Eq.symm
  assumption


abbrev Group.non_neutrals (g : Group G):= {x : G // x ≠ 𝟙}


class AbelianGroup (G: Type) extends (Group G) where
  comm : ∀ a b : G, a ◾ b = b ◾ a

attribute [simp] AbelianGroup.comm

instance : CoeSort (AbelianGroup G) (Type) where
  coe _ := G

instance [g: AbelianGroup G]: Std.Commutative (α := G) Operation.op := ⟨g.comm⟩

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
  exists a⁻ ◾ b
  simp
  apply And.intro
  have := g.inverse_right
  simp [<-g.assoc, g.inverse_right, g.neutral_left]
  intro c hc
  simp [<-hc, <-g.assoc, g.inverse_left, g.neutral_left]


theorem mulWithInversesLeft (g: Group G) {a b : G}  : ∃! x : G, x ◾ a = b := by
  unfold existsUnique
  exists b ◾ a⁻
  simp
  intro y h
  have h := congrArg (. ◾ a⁻) h
  simp at h
  simp_all



abbrev SubGroup [G: Group G] (prop: G -> Prop) (inh: Inhabited (Subtype prop)) (closed: ∀ a b : Subtype prop, prop (a ◾ b⁻)):
Group (Subtype prop) :=
  let neutral := by
    exists 𝟙
    have := closed inh.default inh.default
    simp_all
  let inv := by
      intro ⟨a, ha⟩
      exists a⁻
      have := closed neutral ⟨a, ha⟩
      simp [neutral] at this
      assumption
  {
    neutral := neutral
    groupInv := inv
    op := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exists a ◾ b
      have := closed ⟨a,ha⟩ (inv ⟨b, hb⟩)
      simp_all [inv]

    assoc := by simp
    neutral_left := by simp [neutral]
    neutral_right := by simp [neutral]
    inverse_left := by simp [neutral, inv]
    inverse_right := by simp [neutral, inv]
  }

abbrev AbelianSubGroup [G: AbelianGroup G] (prop: G -> Prop) (inh: Inhabited (Subtype prop)) (closed: ∀ a b : Subtype prop, prop (a ◾ b⁻)):
AbelianGroup (Subtype prop) := {
  toGroup := SubGroup prop inh closed
  comm := by simp [Operation.op]
}


section
structure GroupHom (G: Group G) (H: Group H) where
  hom :  G → H
  property: ∀ a b: G, hom (a ◾ b) = hom a ◾ hom b

attribute[simp] GroupHom.property

variable [G: Group G] [H: Group H]

instance : CoeFun (GroupHom G H) (λ_ => (G -> H)) where
  coe hom := hom.hom


@[simp] theorem GroupHom.neutral (hom: GroupHom G H): hom 𝟙 = 𝟙 := by
  apply Eq.symm
  calc 𝟙
    _ = hom 𝟙 ◾ (hom 𝟙)⁻ := by simp
      _ = hom (𝟙 ◾ 𝟙) ◾ (hom 𝟙)⁻ := by simp
      _ = hom 𝟙 ◾ hom 𝟙 ◾ (hom 𝟙)⁻ := by rw [hom.property]
      _ = hom 𝟙 := by simp
@[simp] theorem GroupHom.inv (hom: GroupHom G H) (a: G): hom a⁻ = (hom a)⁻ := by
  have := calc hom a⁻ ◾ hom a
    _ = hom (a⁻ ◾ a) := by simp [<-hom.property]
    _ = 𝟙 := by simp
  have := Group.inv_unique (hom a) (hom a)⁻ (hom a⁻)
  simp_all




def GroupHom.kernel (hom: GroupHom G H) := {x : G // hom x = 𝟙}

instance HomKernelSubgroup (hom: GroupHom G H): Group hom.kernel := by
  apply SubGroup
  · exists 𝟙
    simp [GroupHom.neutral]
  · intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [ha, hb]

end section
