import Hindman168.RoughFiniteVanDerWaerden
import Hindman168.RoughAffinePolynomial

namespace Hindman168
open Polynomial

theorem rough_constant_term_thinning (q H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀ P : ℝ[X], P.natDegree ≤ q →
      ∃ a b : ℕ, ∃ M : ℚ[X], 0 < b ∧ b ≤ N ∧
        (∀ z : ℕ, z < H → a + b * z < N) ∧ M.natDegree ≤ q ∧
        (∀ j, (M.coeff j).den ∣ q.factorial) ∧
        ∀ z : ℕ, z < H →
          M.eval (z : ℚ) = (⌊P.eval ((a + b * z : ℕ) : ℝ)⌋ : ℚ) ∧
          0 ≤ P.eval ((a + b * z : ℕ) : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) ∧
          P.eval ((a + b * z : ℕ) : ℝ) - ((M.eval (z : ℚ) : ℚ) : ℝ) < 1 := by
  obtain ⟨N, hN, hcolors⟩ := rough_finite_van_der_waerden H hH (Fin (2 ^ (q + 2)))
  refine ⟨N, hN, ?_⟩
  intro P hP
  obtain ⟨a, b, c, hb, hbN, hc⟩ := hcolors (fun z => roughFractionalColor q (P.eval (z : ℝ)))
  let Q := P.comp (C (a : ℝ) + C (b : ℝ) * X)
  have hQ : Q.natDegree ≤ q := (rough_affine_comp_degree P (a : ℝ) (b : ℝ)).trans hP
  have hmono : ∀ z : ℕ, z < H → roughFractionalColor q (Q.eval (z : ℝ)) = c := by
    intro z hz
    simpa only [Q, rough_affine_comp_eval] using (hc z hz).2
  obtain ⟨M, hM, hden, hval⟩ := rough_constant_term_model_of_one_color Q q H hQ c hmono
  refine ⟨a, b, M, hb, hbN, fun z hz => (hc z hz).1, hM, hden, ?_⟩
  intro z hz
  simpa only [Q, rough_affine_comp_eval] using hval z hz

end Hindman168
