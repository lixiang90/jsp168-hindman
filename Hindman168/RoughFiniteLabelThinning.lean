import Hindman168.RoughFiniteVanDerWaerden
import Hindman168.MasterScales

namespace Hindman168
open scoped Classical

theorem rough_finite_label_thinning (H : ℕ) (hH : 0 < H) (κ : Type*) [Finite κ] :
    ∃ N : ℕ, 0 < N ∧ ∀ P : ℕ → κ → Prop,
      (∀ z : ℕ, z < N → ∃ k : κ, P z k) →
      ∃ a b : ℕ, ∃ k : κ, 0 < b ∧ b ≤ N ∧
        ∀ z : ℕ, z < H → a+b*z < N ∧ P (a+b*z) k := by
  obtain ⟨N, hN, hmono⟩ := rough_finite_van_der_waerden H hH κ
  refine ⟨N, hN, ?_⟩
  intro P hP
  obtain ⟨k0, _⟩ := hP 0 hN
  have hex : ∀ z : ℕ, ∃ k : κ, z < N → P z k := by
    intro z
    by_cases hz : z < N
    · obtain ⟨k, hk⟩ := hP z hz
      exact ⟨k, fun _ => hk⟩
    · exact ⟨k0, fun hh => (hz hh).elim⟩
  choose labels hlabels using hex
  obtain ⟨a, b, k, hb, hbN, hc⟩ := hmono labels
  refine ⟨a, b, k, hb, hbN, ?_⟩
  intro z hz
  obtain ⟨hi, he⟩ := hc z hz
  exact ⟨hi, he ▸ hlabels (a+b*z) hi⟩

theorem rough_smooth_progression_reparametrization
    (w N H t m a b : ℕ) (S : ℝ) (hm : 0 < m) (hb : 0 < b)
    (hbN : b ≤ N) (hNw : N ≤ w)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ m → p ≤ w)
    (hindex : ∀ z : ℕ, z < H → a+b*z < N)
    (hsize : ∀ z : ℕ, z < N → S ≤ (t+m*z : ℕ) ∧ (t+m*z : ℕ) < 2*S)
    (hrough : ∀ z : ℕ, z < N → (primorial w).Coprime (t+m*z)) :
    0 < b*m ∧ (∀ p : ℕ, p.Prime → p ∣ b*m → p ≤ w) ∧
      ∀ z : ℕ, z < H →
        (t+m*a)+(b*m)*z = t+m*(a+b*z) ∧
        S ≤ ((t+m*a)+(b*m)*z : ℕ) ∧ ((t+m*a)+(b*m)*z : ℕ) < 2*S ∧
        (primorial w).Coprime ((t+m*a)+(b*m)*z) := by
  refine ⟨Nat.mul_pos hb hm, ?_, ?_⟩
  · intro p hp hdiv
    rcases hp.dvd_mul.mp hdiv with hpb | hpm
    · exact (Nat.le_of_dvd hb hpb).trans (hbN.trans hNw)
    · exact hsmooth p hp hpm
  · intro z hz
    have he : (t+m*a)+(b*m)*z = t+m*(a+b*z) := by ring
    exact ⟨he, he ▸ (hsize (a+b*z) (hindex z hz)).1,
      he ▸ (hsize (a+b*z) (hindex z hz)).2,
      he ▸ hrough (a+b*z) (hindex z hz)⟩

end Hindman168
