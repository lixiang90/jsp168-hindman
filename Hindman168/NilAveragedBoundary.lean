import Hindman168.NilDivisorBoundary
import Hindman168.DivisorMaskExpansion
import Hindman168.HarmonicDivisorMass

/-! Finite Fubini applies the uniform boundary estimate to the actual
harmonic divisor law. The raw root law and divisor law are both retained;
no conditioning or boundary-dependent renormalization is performed. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

theorem divisorMask_boundary_fubini (μ : Mass ℤ) (ρ : Mass ℕ) (R H : ℕ) :
    expectation μ (fun y => if ¬ intervalInteriorRoot R H y then integerDivisorMask ρ y else 0) =
      expectation ρ (fun σ => expectation μ (divisorBoundaryTest σ R H)) := by
  have he (y : ℤ) : (if ¬ intervalInteriorRoot R H y then integerDivisorMask ρ y else 0) =
      expectation ρ (fun σ => divisorBoundaryTest σ R H y) := by
    rw [integerDivisorMask_expectation]
    by_cases hy : intervalInteriorRoot R H y
    · simp only [hy, not_true_eq_false, if_false, divisorBoundaryTest, and_false,
        expectation_const, mul_zero]
    · simp only [hy, not_false_eq_true, if_true, divisorBoundaryTest, and_true]
  simp_rw [he]
  exact expectation_comm μ ρ _

theorem integerMass_divisorMask_boundary_bound {X W K R H d J : ℕ}
    (ρ : Mass ℕ) (hρ : ∀ σ, 0 ≤ ρ σ) (ht : total ρ = 1)
    (hs : ∀ σ ∈ ρ.support, 0 < σ ∧ σ ≤ K ∧ W.Coprime σ)
    (hX : 2 ≤ X) (hW : 0 < W) (hR : 0 < R) (hJ : 0 < J)
    (hmargin : J * H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W)
      (fun y => if ¬ intervalInteriorRoot R H y then integerDivisorMask ρ y else 0) ≤
      4 * (d : ℝ) / J + (4 + 8 * (d : ℝ)) * (W * K : ℕ) / R +
        (W * K : ℕ) * ((R : ℝ) + 1) / X := by
  rw [divisorMask_boundary_fubini]
  calc
    _ ≤ expectation ρ (fun _ => 4 * (d : ℝ) / J +
      (4 + 8 * (d : ℝ)) * (W * K : ℕ) / R + (W * K : ℕ) * ((R : ℝ) + 1) / X) := by
      apply expectation_mono_support _ _ _ hρ
      intro σ hσ
      obtain ⟨hp, hk, hc⟩ := hs σ hσ
      exact integerMass_divisorBoundary_uniform_bound hX hW hp hk hR hJ hc hmargin hlog hWX
    _ = _ := by rw [expectation_const, ht, one_mul]

theorem integerMass_onePlusDivisor_boundary_bound {X W K R H d J : ℕ}
    (ρ : Mass ℕ) (hρ : ∀ σ, 0 ≤ ρ σ) (ht : total ρ = 1)
    (hs : ∀ σ ∈ ρ.support, 0 < σ ∧ σ ≤ K ∧ W.Coprime σ) (hK : 1 ≤ K)
    (hX : 2 ≤ X) (hW : 0 < W) (hR : 0 < R) (hJ : 0 < J)
    (hmargin : J * H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W)
      (fun y => if ¬ intervalInteriorRoot R H y then 1 + integerDivisorMask ρ y else 0) ≤
      8 * (d : ℝ) / J + 2 * ((4 + 8 * (d : ℝ)) * (W * K : ℕ) / R +
        (W * K : ℕ) * ((R : ℝ) + 1) / X) := by
  have hb := integerMass_divisorMask_boundary_bound ρ hρ ht hs hX hW hR hJ hmargin hlog hWX
  have h1 := integerMass_divisorBoundary_uniform_bound (σ := 1)
    hX hW (by decide) hK hR hJ (by simp) hmargin hlog hWX
  have he (y : ℤ) : (if ¬ intervalInteriorRoot R H y then 1 + integerDivisorMask ρ y else 0) =
      divisorBoundaryTest 1 R H y +
        (if ¬ intervalInteriorRoot R H y then integerDivisorMask ρ y else 0) := by
    by_cases hy : intervalInteriorRoot R H y <;> simp [divisorBoundaryTest, hy]
  simp_rw [he]
  rw [expectation_add]
  exact (add_le_add h1 hb).trans_eq (by ring)

theorem harmonicDivisorMass_onePlus_boundary_bound {κ : Type*} [Fintype κ]
    (xs : κ → ℕ) {X W K R H d J : ℕ}
    (hx : ∀ j, 2 ≤ xs j) (hH : ∀ j, 0 < harmonicNormalizer (xs j) W)
    (hcap : (∏ j, xs j ^ 2) ≤ K) (hK : 1 ≤ K)
    (hX : 2 ≤ X) (hW : 0 < W) (hR : 0 < R) (hJ : 0 < J)
    (hmargin : J * H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W)
      (fun y => if ¬ intervalInteriorRoot R H y then
        1 + integerDivisorMask (harmonicDivisorMass xs W) y else 0) ≤
      8 * (d : ℝ) / J + 2 * ((4 + 8 * (d : ℝ)) * (W * K : ℕ) / R +
        (W * K : ℕ) * ((R : ℝ) + 1) / X) := by
  apply integerMass_onePlusDivisor_boundary_bound _
    (harmonicDivisorMass_nonneg xs W hH) (harmonicDivisorMass_total xs W hH)
    _ hK hX hW hR hJ hmargin hlog hWX
  intro σ hσ
  obtain ⟨hp, hk, hc⟩ := harmonicDivisorMass_support xs W hx hσ
  exact ⟨hp, hk.trans hcap, hc.symm⟩

theorem tailMass_onePlus_boundary_bound (xs : List ℕ) {X W K R H d J : ℕ}
    (hv : ValidCutoffs xs W) (hcap : tailBound xs ≤ K) (hK : 1 ≤ K)
    (hX : 2 ≤ X) (hW : 0 < W) (hR : 0 < R) (hJ : 0 < J)
    (hmargin : J * H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W)
      (fun y => if ¬ intervalInteriorRoot R H y then
        1 + integerDivisorMask (tailMass W xs) y else 0) ≤
      8 * (d : ℝ) / J + 2 * ((4 + 8 * (d : ℝ)) * (W * K : ℕ) / R +
        (W * K : ℕ) * ((R : ℝ) + 1) / X) := by
  apply integerMass_onePlusDivisor_boundary_bound _
    (tailMass_nonneg hW xs hv) (tailMass_total hW xs hv)
    _ hK hX hW hR hJ hmargin hlog hWX
  intro σ hσ
  obtain ⟨hp, hk, hc⟩ := tailMass_support xs hv σ hσ
  exact ⟨hp, hk.trans hcap, hc⟩

end Hindman168
