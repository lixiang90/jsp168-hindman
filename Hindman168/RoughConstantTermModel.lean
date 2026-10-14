import Hindman168.RoughFloorDifferences
import Hindman168.RoughNewtonDenominators
import Mathlib.Data.Nat.Prime.Factorial

namespace Hindman168
open Polynomial

theorem rough_constant_term_model (P : ℝ[X]) (q H : ℕ) (hP : P.natDegree ≤ q)
    (a delta : ℝ) (hsmall : (2 : ℝ) ^ (q + 1) * delta < 1)
    (hbin : ∀ z : ℕ, z < H → a ≤ Int.fract (P.eval (z : ℝ)) ∧
      Int.fract (P.eval (z : ℝ)) ≤ a + delta) :
    ∃ M : ℚ[X], M.natDegree ≤ q ∧
      (∀ j, (M.coeff j).den ∣ q.factorial) ∧
      ∀ z : ℕ, z < H → M.eval (z : ℚ) = (⌊P.eval (z : ℝ)⌋ : ℚ) ∧
        0 ≤ P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) ∧
        P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) < 1 := by
  let f : ℕ → ℤ := fun z => ⌊P.eval (z : ℝ)⌋
  have hd := rough_floor_differences_on_interval P q H hP a delta hsmall hbin
  have hm := roughNewtonPolynomial_matches f q H hd
  refine ⟨roughNewtonPolynomial f q, roughNewtonPolynomial_degree f q,
    roughNewtonPolynomial_den_dvd f q, ?_⟩
  intro z hz
  refine ⟨hm z hz, ?_⟩
  rw [hm z hz, Rat.cast_intCast]
  change 0 ≤ P.eval (z : ℝ) - (⌊P.eval (z : ℝ)⌋ : ℝ) ∧
    P.eval (z : ℝ) - (⌊P.eval (z : ℝ)⌋ : ℝ) < 1
  rw [Int.self_sub_floor]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem rough_constant_term_model_smooth (P : ℝ[X]) (q H w : ℕ)
    (hP : P.natDegree ≤ q) (hqw : q ≤ w)
    (a delta : ℝ) (hsmall : (2 : ℝ) ^ (q + 1) * delta < 1)
    (hbin : ∀ z : ℕ, z < H → a ≤ Int.fract (P.eval (z : ℝ)) ∧
      Int.fract (P.eval (z : ℝ)) ≤ a + delta) :
    ∃ M : ℚ[X], M.natDegree ≤ q ∧
      (∀ j p, p.Prime → p ∣ (M.coeff j).den → p ≤ w) ∧
      ∀ z : ℕ, z < H → M.eval (z : ℚ) = (⌊P.eval (z : ℝ)⌋ : ℚ) ∧
        0 ≤ P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) ∧
        P.eval (z : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) < 1 := by
  obtain ⟨M, hdeg, hden, hval⟩ := rough_constant_term_model P q H hP a delta hsmall hbin
  refine ⟨M, hdeg, ?_, hval⟩
  intro j p hp hpd
  exact (hp.dvd_factorial.mp (hpd.trans (hden j))).trans hqw

end Hindman168
