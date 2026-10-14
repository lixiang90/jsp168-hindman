import Hindman168.AlignmentCubeArrayExponent
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Hindman168
open scoped BigOperators
open MvPolynomial

noncomputable def alignmentCubeExponentPolynomial {ε : Type*} [Fintype ε]
    (M Y r rv s : ℚ) (q rho : ε → ℚ) : MvPolynomial (Option (Option ε)) ℚ :=
  C (Y + (r - rv) / M) + X none + C (s / M) * X (some none) +
    ∑ e, (C (q e / M) * X (some (some e)) -
      C (rho e / M) * X (some none) * X (some (some e)))

theorem alignmentCubeExponentPolynomial_degree {ε : Type*} [Fintype ε]
    (M Y r rv s : ℚ) (q rho : ε → ℚ) :
    (alignmentCubeExponentPolynomial M Y r rv s q rho).totalDegree ≤ 2 := by
  unfold alignmentCubeExponentPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      simp only [totalDegree_C, totalDegree_X]
      decide
    · exact (totalDegree_mul _ _).trans (by simp)
  · apply totalDegree_finsetSum_le
    intro e _
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simp)
    · have h := totalDegree_mul (C (rho e / M) : MvPolynomial (Option (Option ε)) ℚ)
        (X (some none))
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, totalDegree_X] at h ⊢
      omega

theorem alignmentCubeExponentPolynomial_eval {ε : Type*} [Fintype ε]
    (M Y r rv s x t : ℚ) (q rho u : ε → ℚ) :
    eval (fun z => match z with | none => x | some none => t | some (some e) => u e)
      (alignmentCubeExponentPolynomial M Y r rv s q rho) =
      x + Y + (r + t * s - rv) / M + ∑ e, u e * ((q e - t * rho e) / M) := by
  simp only [alignmentCubeExponentPolynomial, map_add, map_sub, map_mul, map_sum,
    eval_C, eval_X]
  have hs : (∑ e, (q e / M * u e - rho e / M * t * u e)) =
      ∑ e, u e * ((q e - t * rho e) / M) := by
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hs]
  ring

theorem alignmentCubeExponentPolynomial_integral_eval {ε : Type*} [Fintype ε]
    (M Y r rv s x t k : ℤ) (hM : M ≠ 0) (q rho u delta : ε → ℤ)
    (hk : M * k = r + t * s - rv)
    (hd : ∀ e, M * delta e = q e - t * rho e) :
    eval (fun z => match z with
      | none => (x : ℚ)
      | some none => (t : ℚ)
      | some (some e) => (u e : ℚ))
      (alignmentCubeExponentPolynomial M Y r rv s (fun e => (q e : ℚ))
        (fun e => (rho e : ℚ))) = ((x + Y + k + ∑ e, u e * delta e : ℤ) : ℚ) := by
  rw [alignmentCubeExponentPolynomial_eval]
  have hm : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have hkc : ((r : ℚ) + t * s - rv) / M = k := by
    apply (div_eq_iff hm).mpr
    exact_mod_cast hk.symm.trans (mul_comm M k)
  have hdc (e : ε) : ((q e : ℚ) - t * rho e) / M = delta e := by
    apply (div_eq_iff hm).mpr
    exact_mod_cast (hd e).symm.trans (mul_comm M (delta e))
  simp only [hkc, hdc, Int.cast_add, Int.cast_sum, Int.cast_mul]

end Hindman168
