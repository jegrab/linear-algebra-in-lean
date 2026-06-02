import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field

class Vectorspace (F: Field F) (V : Type) extends AbelianGroup V, SMul F V where
  one_mul : ∀ v: V, (1:F) • v = v
  s_assoc : ∀ (r s: F) (v : V), r • (s • v) = (r * s) • v
  s_distr_left : ∀ (r s : F) (v : V), (r+s)•v = (r•v) + (s•v)
  s_distr_right : ∀ (r: F) (v w : V), r•(v+w) = (r•v) + (r•w)

attribute[simp] Vectorspace.one_mul Vectorspace.s_assoc Vectorspace.s_distr_left Vectorspace.s_distr_right

namespace Vectorspace


@[simp] theorem smul_zero_right [F: Field FF]  [Vectorspace F V] (r : F) : r • (0: V) = 0 := by
  have h : r • (0 + (0:V)) = r • 0 + r • 0 := by rw [<-s_distr_right]
  have h : r • (0:V) = r • 0 + r • 0 := by simp [<-h]
  exact Group.eq_zero_of_add_eq_self (Eq.symm h)

@[simp] theorem smul_zero_left [F: Field FF]  [Vectorspace F V] (v : V) : (0:F) • v = 0 := by
  have := calc v
          _ = (1 + 0: F) • v := by simp
          _ = (1:F) • v + (0:F) • v := by rw [s_distr_left]
          _ = v + (0:F) • v := by simp
  exact Group.eq_zero_of_add_eq_self_right (Eq.symm this)

@[simp] theorem zero_div_free [F: Field FF]  [Vectorspace F V] (r : F) (v : V) (h: r • v = 0) : r = 0 ∨ v = 0 := by
  by_cases hr: r = 0
  . left
    assumption
  . right
    have h₂ : v = (1:F) • v := by simp
    let rn: F.non_zeros := ⟨r,hr⟩
    have : rn⁻¹.val * rn = 1 := by rw [Field.mul_inverse_left]
    rw [<-this] at h₂
    rw [<-s_assoc] at h₂
    rw [h] at h₂
    rw [smul_zero_right] at h₂
    exact h₂











end Vectorspace
