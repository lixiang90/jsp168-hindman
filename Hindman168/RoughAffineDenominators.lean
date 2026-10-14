import Hindman168.RoughSmoothDenominatorSupport

namespace Hindman168
open Polynomial

theorem roughDenominatorSubring_mem_of_prime_support (w : ℕ) (x : ℚ)
    (h : ∀ p, p.Prime → p ∣ x.den → p ≤ w) :
    x ∈ roughDenominatorSubring (primorial w) := by
  apply roughDenominatorSubring_mem_of_dvd (primorial w) x.den x.den
    (rough_smooth_integer_dvd_primorial_power x.den_ne_zero h)
  refine ⟨x.num, ?_⟩
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hh := congrArg (fun r : ℚ => (x.den : ℚ) * r) x.num_div_den.symm
  simpa only [mul_div_cancel₀ _ hd] using hh

theorem rough_subring_affine_comp_coeff (S : Subring ℚ) (P : ℚ[X])
    (hP : ∀ j, P.coeff j ∈ S) (a b : ℤ) :
    ∀ j, (P.comp (C (a : ℚ) + C (b : ℚ) * X)).coeff j ∈ S := by
  obtain ⟨p, hp⟩ := (mem_lifts P).mp (rough_polynomial_lift_subring S P hP)
  let aa : S := ⟨(a : ℚ), intCast_mem S a⟩
  let bb : S := ⟨(b : ℚ), intCast_mem S b⟩
  have hmap : (p.comp (C aa + C bb * X)).map S.subtype =
      P.comp (C (a : ℚ) + C (b : ℚ) * X) := by
    simp only [map_comp, Polynomial.map_add, Polynomial.map_mul, map_C, map_X, hp]
    rfl
  intro j
  have hh := congrArg (fun Q : ℚ[X] => Q.coeff j) hmap
  rw [coeff_map] at hh
  rw [← hh]
  exact ((p.comp (C aa + C bb * X)).coeff j).property

theorem rough_affine_comp_prime_support (w : ℕ) (P : ℚ[X])
    (hP : ∀ j p, p.Prime → p ∣ (P.coeff j).den → p ≤ w) (a b : ℤ) :
    ∀ j p, p.Prime → p ∣ ((P.comp (C (a : ℚ) + C (b : ℚ) * X)).coeff j).den → p ≤ w := by
  have hc := rough_subring_affine_comp_coeff (roughDenominatorSubring (primorial w)) P
    (fun j => roughDenominatorSubring_mem_of_prime_support w (P.coeff j) (hP j)) a b
  intro j
  exact roughDenominatorSubring_prime_support (hc j)

end Hindman168
