import Hindman168.RoughPolynomialExactDivision
import Mathlib.Algebra.Polynomial.Lifts

namespace Hindman168
open Polynomial

theorem rough_polynomial_lift_subring (S : Subring ℚ) (R : ℚ[X])
    (hR : ∀ j, R.coeff j ∈ S) : R ∈ lifts S.subtype := by
  apply (lifts_iff_coeff_lifts R).mpr
  intro j
  exact ⟨⟨R.coeff j, hR j⟩, rfl⟩

theorem rough_monic_quotient_coeff_mem (S : Subring ℚ) (R Q : ℚ[X])
    (hR : ∀ j, R.coeff j ∈ S) (hQ : ∀ j, Q.coeff j ∈ S) (hmonic : Q.Monic) :
    ∀ j, (R /ₘ Q).coeff j ∈ S := by
  obtain ⟨r, hr⟩ := (mem_lifts R).mp (rough_polynomial_lift_subring S R hR)
  obtain ⟨q, hq, _, hqm⟩ := lifts_and_degree_eq_and_monic
    (rough_polynomial_lift_subring S Q hQ) hmonic
  have hmap : (r /ₘ q).map S.subtype = R /ₘ Q := by
    rw [map_divByMonic S.subtype hqm, hr, hq]
  intro j
  have h := congrArg (fun p : ℚ[X] => p.coeff j) hmap
  rw [coeff_map] at h
  rw [← h]
  exact ((r /ₘ q).coeff j).property

theorem rough_affine_quotient_coeff_mem (S : Subring ℚ) (R M : ℚ[X])
    (t m : ℚ) (hm : m ≠ 0) (ht : t ∈ S) (hmi : m⁻¹ ∈ S) (e : ℕ)
    (hR : ∀ j, R.coeff j ∈ S) (hfactor : R = (C t + C m * X) ^ e * M) :
    ∀ j, M.coeff j ∈ S := by
  let a : S := ⟨t / m, by simpa only [div_eq_mul_inv] using S.mul_mem ht hmi⟩
  have hQ : ∀ j, ((X + C (t / m)) ^ e : ℚ[X]).coeff j ∈ S := by
    intro j
    have hmap : (((X + C a) ^ e : S[X]).map S.subtype) = (X + C (t / m)) ^ e := by
      simp only [Polynomial.map_pow, Polynomial.map_add, map_X, map_C]
      rfl
    have h := congrArg (fun p : ℚ[X] => p.coeff j) hmap
    rw [coeff_map] at h
    rw [← h]
    exact (((X + C a) ^ e : S[X]).coeff j).property
  have ha : C t + C m * X = C m * (X + C (t / m)) := by
    rw [mul_add, ← C_mul, mul_div_cancel₀ t hm]
    ring
  have hr : R = (X + C (t / m)) ^ e * (C (m ^ e) * M) := by
    rw [hfactor, ha, mul_pow, ← C_pow]
    ring
  have hdiv : R /ₘ (X + C (t / m)) ^ e = C (m ^ e) * M := by
    rw [hr, mul_divByMonic_cancel_left _ ((monic_X_add_C _).pow e)]
  have hn := rough_monic_quotient_coeff_mem S R ((X + C (t / m)) ^ e) hR hQ
    ((monic_X_add_C _).pow e)
  intro j
  have hc := hn j
  rw [hdiv, coeff_C_mul] at hc
  have h := S.mul_mem (S.pow_mem hmi e) hc
  have heq : (m⁻¹) ^ e * (m ^ e * M.coeff j) = M.coeff j := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hm, one_pow, one_mul]
  rwa [heq] at h

end Hindman168
