import Hindman168.RoughConstantTermThinning
import Hindman168.RoughModelReparametrization

namespace Hindman168
open Polynomial

theorem rough_joint_coefficient_thinning {ι : Type*} (s : Finset ι)
    (q0 H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w q : ℕ) (e : ι → ℕ) (Z K : ℝ)
      (theta : ι → ℝ[X]) (M : ι → ℚ[X]) (P : ℝ[X]), N ≤ w → P.natDegree ≤ q0 →
      (∀ i ∈ s, RoughCoefficientModel w N q (e i) Z K (theta i) (M i)) →
      ∃ a b : ℕ, ∃ M0 : ℚ[X], 0 < b ∧ b ≤ N ∧
        (∀ z : ℕ, z < H → a + b * z < N) ∧ M0.natDegree ≤ q0 ∧
        (∀ j p, p.Prime → p ∣ (M0.coeff j).den → p ≤ w) ∧
        (∀ z : ℕ, z < H → M0.eval (z : ℚ) = (⌊P.eval ((a + b * z : ℕ) : ℝ)⌋ : ℚ) ∧
          0 ≤ P.eval ((a + b * z : ℕ) : ℝ) - ((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
          P.eval ((a + b * z : ℕ) : ℝ) - ((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) ∧
        ∀ i ∈ s, RoughCoefficientModel w H q (e i) Z K
          ((theta i).comp (C (a : ℝ) + C (b : ℝ) * X))
          ((M i).comp (C (a : ℚ) + C (b : ℚ) * X)) := by
  obtain ⟨N0, hN0, hthin⟩ := rough_constant_term_thinning q0 H hH
  refine ⟨max N0 q0, lt_of_lt_of_le hN0 (le_max_left _ _), ?_⟩
  intro w q e Z K theta M P hNw hP hmodels
  obtain ⟨a, b, M0, hb, hbN, hindex, hdeg, hden, hval⟩ := hthin P hP
  have hindex' : ∀ z : ℕ, z < H → a + b * z < max N0 q0 :=
    fun z hz => (hindex z hz).trans_le (le_max_left _ _)
  refine ⟨a, b, M0, hb, hbN.trans (le_max_left _ _), hindex', hdeg, ?_, hval, ?_⟩
  · intro j p hp hpd
    exact (hp.dvd_factorial.mp (hpd.trans (hden j))).trans ((le_max_right N0 q0).trans hNw)
  · intro i hi
    exact rough_coefficient_model_reparametrize (hmodels i hi) hindex'

end Hindman168
