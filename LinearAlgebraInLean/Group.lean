import LinearAlgebraInLean.Infix
import LinearAlgebraInLean.Util

abbrev neutral_pred (op : G -> G -> G) (n : G) := ∀ a : G, (op a n = a ∧ op n a = a)

theorem unique_neutral (ha : neutral_pred op a) (hb : neutral_pred op b) : a = b :=
  let ⟨h1,_⟩ := hb a
  let ⟨_,h2⟩ := ha b
  let h1 := Eq.comm.mp h1
  Eq.trans h1 h2

abbrev operation (G: Type u): Type u:= G -> G -> G

class Group (G: Type u) extends Add G, Neg G, Zero G where
  assoc : ∀ a b c : G , (a + b) + c = a + (b + c)
  neutral_right : ∀ a : G , a + 0 = a
  neutral_left : ∀ a: G , 0 + a = a
  inverse_right : ∀ a : G, a + (-a) = 0
  inverse_left : ∀ a : G, (-a) + a = 0

instance [Group G] : Sub G where
  sub a b := a + (-b)

instance: CoeSort (Group G) (Type) where
  coe _ := G

instance [g: Group G]: Std.Associative (α := G) (. + .) := ⟨g.assoc⟩

attribute [simp] Group.assoc Group.neutral_right Group.neutral_left Group.inverse_left Group.inverse_right



abbrev GroupFromRight [Add G] [Neg G] [Zero G]
(assoc: ∀ a b c : G , (a + b) + c = a +  (b + c))
(neutral_right: ∀ a : G , a + 0 = a)
(inverse_right:  ∀ a : G, a + (-a) = 0)
: Group G where
  assoc := assoc
  inverse_right := inverse_right
  neutral_right := neutral_right
  neutral_left := by
    intro a
    apply Eq.symm
    calc a
      _ = a + 0 := by rw [neutral_right]
      _ = a + -a + - -a := by rw [assoc, inverse_right]
      _ = 0 + - - a  := by rw [inverse_right]
      _ = 0 + a := by grind
  inverse_left := by
    intro a
    apply Eq.symm
    calc 0
      _ = -a + a + -(-a + a) := by rw [inverse_right]
      _ = -a + a + -a + a := by grind
      _ = -a + a := by conv => lhs; lhs; rw [assoc, inverse_right, neutral_right]

namespace Group
variable [G: Group G]

theorem neg_unique {a b: G}: a + b = 0 -> b = -a := by
  intro h
  have := congrArg (-a + .) h
  simp [<-Group.assoc] at this
  assumption

theorem neg_unique_left {a b: G}: b + a = 0 -> b = -a := by
  intro h
  have := congrArg (. + -a) h
  simp at this
  assumption

@[simp] theorem neg_neutral: -(0: G) = 0 := by
  have : (0:G) + 0 = 0 := by simp
  have := Group.neg_unique this
  apply Eq.symm
  assumption

@[simp] theorem neg_neg {a: G}: - - a = a := by
  have : -a + a = 0 := by simp
  have := Group.neg_unique this
  apply Eq.symm
  assumption

theorem neutral_unique {a e: G} : a + e = a -> e = 0 := by
  have (a: G) : unique (fun x => a + x = a) := by
    unfold unique
    simp
    intro b₁ b₂ h₁ h₂
    calc b₁
      _ = -a + a + b₁ := by simp
      _ = -a + (a + b₁) := by simp [<-Group.assoc]
      _ = -a + (a + b₂) := by simp[h₁, h₂]
      _ = (-a + a) + b₂ := by simp [<-Group.assoc]
      _ = b₂ := by simp
  intro h
  apply this a e 0 h (Group.neutral_right _)


@[simp] theorem a_sub_a_is_zero {a : G} : a - a = 0 := by
  simp [HSub.hSub, Sub.sub]

@[simp] theorem sub_is_add_neg{a b: G}: a - b = a + -b := by
  simp [HSub.hSub, Sub.sub]

@[simp] theorem sub_sum {a b: G}: -(a + b) = -b + -a := by
  have := calc (a + b) + (-b + -a)
    _ = a + (b + -b) + -a := by rw[G.assoc]; conv => rhs; rw [G.assoc]; rhs; rw [G.assoc]
    _ = 0 := by simp
  exact (Group.neg_unique this).symm

@[simp] theorem sub_sub_swap {a b c: G}: a - (b - c) = a + c - b := by
  simp

end Group

abbrev Group.non_zeros (g : Group G):= {x : G // x ≠ 0}


class AbelianGroup (G: Type) extends (Group G) where
  comm : ∀ a b : G, a + b = b + a

attribute [simp] AbelianGroup.comm

instance : CoeSort (AbelianGroup G) (Type) where
  coe _ := G

instance [g: AbelianGroup G]: Std.Commutative (α := G) (. + .) := ⟨g.comm⟩

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

-- theorem Group.mulWithInversesRight [g: Group G] {a b : g}  : ∃! x : G, a + x = b := by
--   unfold existsUnique
--   exists -a + b
--   simp
--   apply And.intro
--   have := g.inverse_right
--   simp [<-g.assoc, g.inverse_right, g.neutral_left]
--   intro c hc
--   simp [<-hc, <-g.assoc, g.inverse_left, g.neutral_left]


-- theorem mulWithInversesLeft (g: Group G) {a b : G}  : ∃! x : G, x + a = b := by
--   unfold existsUnique
--   exists b + -a
--   simp
--   intro y h
--   have h := congrArg (. + -a) h
--   simp at h
--   simp_all



abbrev SubGroup [G: Group G] (prop: G -> Prop) (inh: Nonempty (Subtype prop)) (closed: ∀ a b : Subtype prop, prop (a + -b)):
Group (Subtype prop) :=
  let neutral : Subtype prop := by
    exists 0
    cases inh
    rename_i inh
    have := closed inh inh
    simp_all
  let inv : Subtype prop -> Subtype prop := by
      intro ⟨a, ha⟩
      exists -a
      have := closed neutral ⟨a, ha⟩
      simp [neutral] at this
      assumption
  let add := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      exists a + b
      have := closed ⟨a,ha⟩ (inv ⟨b, hb⟩)
      simp_all [inv]
  {
    zero := neutral
    neg := inv
    add := add
    assoc := by
      simp [HAdd.hAdd]
      simp [add]
    neutral_left := by
      simp [HAdd.hAdd]
      simp [add, OfNat.ofNat]
      simp [neutral]
    neutral_right := by
      simp [HAdd.hAdd]
      simp [add, OfNat.ofNat]
      simp [neutral]
    inverse_left := by
      simp [HAdd.hAdd]
      simp [add, inv, OfNat.ofNat, neutral]

    inverse_right := by
      simp [HAdd.hAdd]
      simp [add, inv, OfNat.ofNat, neutral]
  }

abbrev AbelianSubGroup [G: AbelianGroup G] (prop: G -> Prop) (inh: Nonempty (Subtype prop)) (closed: ∀ a b : Subtype prop, prop (a + (-b))):
AbelianGroup (Subtype prop) := {
  toGroup := SubGroup prop inh closed
  comm := by
    simp [HAdd.hAdd]
    simp [Add.add]
}


section
structure GroupHom (G: Group G) (H: Group H) where
  hom :  G → H
  add: ∀ a b: G, hom (a + b) = hom a + hom b

attribute[simp] GroupHom.add

variable [G: Group G] [H: Group H]

instance : CoeFun (GroupHom G H) (λ_ => (G -> H)) where
  coe hom := hom.hom


def GroupHom.ext {f g: GroupHom G H}: (∀ x, f x = g x) → f = g := by
  intro h
  cases f <;> cases g
  simp at *
  funext
  apply h


@[simp] theorem GroupHom.zero (hom: GroupHom G H): hom 0 = 0 := by
  apply Eq.symm
  calc 0
    _ = hom 0 + -(hom 0) := by simp
      _ = hom (0 + 0) + -(hom 0) := by simp
      _ = hom 0 + hom 0 + -(hom 0) := by rw [hom.add]
      _ = hom 0 := by simp
@[simp] theorem GroupHom.neg (hom: GroupHom G H) (a: G): hom (-a) = -(hom a) := by
  have := calc hom (-a) + hom a
    _ = hom (-a + a) := by simp [<-hom.add]
    _ = 0 := by simp
  have := Group.neg_unique this
  simp_all




def GroupHom.kernel (hom: GroupHom G H) := {x : G // hom x = 0}

instance HomKernelSubgroup (hom: GroupHom G H): Group hom.kernel := by
  apply SubGroup
  · exists 0
    simp [GroupHom.zero]
  · intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [ha, hb]

end section
