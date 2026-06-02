import LinearAlgebraInLean.Group
import LinearAlgebraInLean.Field

class Vectorspace (F: Field F) (V : Type) extends AbelianGroup V, SMul F V where
  one_mul : ∀ v: V, (1:F) • v = v
  s_assoc : ∀ (r s: F) (v : V), r • (s • v) = (r * s) • v
  s_distr_left : ∀ (r s : F) (v : V), (r+s)•v = (r•v) + (s•v)
  s_distr_right : ∀ (r: F) (v w : V), r•(v+w) = (r•v) + (r•w)

attribute[simp] Vectorspace.one_mul Vectorspace.s_assoc Vectorspace.s_distr_left Vectorspace.s_distr_right

namespace Vectorspace


theorem smul_zero [F: Field FF]  [Vectorspace F V] (r : F) : r • (0: V) = 0 := by
  have h : r • (0 + (0:V)) = r • 0 + r • 0 := by rw [<-s_distr_right]
  have h : r • (0:V) = r • 0 + r • 0 := by simp [<-h]
  sorry

theorem zero_div_free [F: Field FF]  [Vectorspace F V] (r : F) (v : V) (h: r • v = 0) : r = 0 ∨ v = 0 := by
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
    rw [smul_zero] at h₂
    exact h₂











end Vectorspace
