import Hindman168.ScalarPolynomialLeadingInverse
import Hindman168.FiniteNaturalBlockMeans
import Hindman168.UnitCircleTopPowerProgression
import Hindman168.ScalarPolynomialTopRemoval
import Hindman168.FiniteComplexUnitFactorTransfer
import Hindman168.PositiveFractionalBlockLength
import Hindman168.ScalarPolynomialStrippingFraction

namespace Hindman168
open Polynomial
open scoped Classical

/-- Genuine short arithmetic progression localization and top-monomial
stripping. All bounds and the length fraction precede the polynomial and N.
The same actual q controls the top coefficient and the selected progression. -/
theorem scalar_polynomial_top_stripping (d : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B M : ℕ, ∃ ρ : ℝ, 0 < B ∧ 0 < M ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ p : ℝ[X], p.natDegree ≤ d+1 → ∀ N : ℕ, M ≤ N →
        δ ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖ →
        ∃ q a H : ℕ, 0 < q ∧ q ≤ B ∧ a < N ∧ H=⌊ρ*(N : ℝ)⌋₊ ∧ 0 < H ∧
          ρ*(N : ℝ)/2 ≤ (H : ℝ) ∧ (H : ℝ) ≤ ρ*(N : ℝ) ∧
          (∀ j < H, a+q*j < N) ∧
          (N : ℝ)^(d+1)*‖(((q : ℝ)*p.coeff (d+1) : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ) ∧
          (scalarPolynomialOnProgression (scalarPolynomialDropTop p (d+1)) a q).natDegree ≤ d ∧
          δ/4 ≤ ‖finiteComplexSetMean (Finset.range H)
            (scalarPolynomialPhase (scalarPolynomialOnProgression (scalarPolynomialDropTop p (d+1)) a q))‖ := by
  obtain ⟨B, hB, htopInv⟩ := scalar_polynomial_phase_leading_inverse d δ hδ hδ1
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨ρ, hρ, hρ1, hwidth, hphase⟩ := scalar_polynomial_stripping_fraction d (B : ℝ) δ hBr hδ hδ1
  let M := ⌈2/ρ⌉₊+1
  have hM : 0 < M := by dsimp only [M]; omega
  have hMbound : 2/ρ ≤ M := (Nat.le_ceil _).trans (by
    exact_mod_cast (show ⌈2/ρ⌉₊ ≤ M by dsimp only [M]; omega))
  refine ⟨B, M, ρ, hB, hM, hρ, hρ1, ?_⟩
  intro p hp N hMN hmean
  have hN : 0 < N := hM.trans_le hMN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hlarge : 2 ≤ ρ*(N : ℝ) := by
    have hb := (div_le_iff₀ hρ).mp (hMbound.trans hMNr)
    nlinarith
  let H := ⌊ρ*(N : ℝ)⌋₊
  obtain ⟨hH, hHlow, hHup⟩ := positive_fractional_floor_length ρ N hlarge
  obtain ⟨q, hq, hqB, htop⟩ := htopInv p hp N hN hmean
  have hqBr : (q : ℝ) ≤ B := by exact_mod_cast hqB
  have hphysical : 4*(q : ℝ)*(H : ℝ) ≤ δ*(N : ℝ) := by
    have hmul := mul_le_mul hqBr hHup (Nat.cast_nonneg H) (by positivity : 0 ≤ (B : ℝ))
    have hw := mul_le_mul_of_nonneg_right hwidth hNr.le
    nlinarith
  obtain ⟨a, ha, hindices, hprog⟩ := finite_complex_short_progression_mean_large
    (scalarPolynomialPhase p) N q H hN hq hH
    (fun n _ => (scalar_polynomial_phase_norm p n).le) δ hδ hphysical hmean
  have hfrac : (H : ℝ)/(N : ℝ) ≤ ρ := by
    apply (div_le_iff₀ hNr).mpr
    exact hHup
  have herr : ∀ j ∈ Finset.range H,
      ‖scalarPolynomialPhase p (a+q*j)-
        (AddCircle.toCircle (((p.coeff (d+1)*(a : ℝ)^(d+1) : ℝ)) : UnitAddCircle) : ℂ)*
          scalarPolynomialPhase (scalarPolynomialDropTop p (d+1)) (a+q*j)‖ ≤ δ/8 := by
    intro j hj
    rw [scalar_polynomial_top_phase_error]
    have hv := unit_circle_top_power_progression_variation (p.coeff (d+1)) (B : ℝ)
      (d+1) N a q j H hN hq (Finset.mem_range.mp hj) ha
      (hindices j (Finset.mem_range.mp hj)) htop
    have hh := mul_le_mul_of_nonneg_left hfrac
      (by positivity : 0 ≤ 2*Real.pi*(d+1 : ℕ)*(B : ℝ))
    have he : 2*Real.pi*(d+1 : ℕ)*(B : ℝ)*(H : ℝ)/(N : ℝ) =
        (2*Real.pi*(d+1 : ℕ)*(B : ℝ))*((H : ℝ)/(N : ℝ)) := by ring
    rw [he] at hv
    exact hv.trans (hh.trans hphase)
  have htransfer := finite_complex_mean_unit_factor_transfer (Finset.range H)
    (fun j => scalarPolynomialPhase p (a+q*j))
    (fun j => scalarPolynomialPhase (scalarPolynomialDropTop p (d+1)) (a+q*j))
    (AddCircle.toCircle (((p.coeff (d+1)*(a : ℝ)^(d+1) : ℝ)) : UnitAddCircle) : ℂ)
    (Circle.norm_coe _) (δ/2) (δ/8) (by positivity) hprog herr
  have hlow : δ/4 ≤ ‖finiteComplexSetMean (Finset.range H)
      (scalarPolynomialPhase (scalarPolynomialOnProgression (scalarPolynomialDropTop p (d+1)) a q))‖ := by
    have he : scalarPolynomialPhase (scalarPolynomialOnProgression (scalarPolynomialDropTop p (d+1)) a q) =
        (fun j => scalarPolynomialPhase (scalarPolynomialDropTop p (d+1)) (a+q*j)) :=
      funext (fun j => scalar_polynomial_on_progression_phase _ a q j)
    rw [he]
    linarith
  exact ⟨q, a, H, hq, hqB, ha, rfl, hH, hHlow, hHup, hindices, htop,
    scalar_polynomial_on_progression_degree _ a q d (scalar_polynomial_drop_top_degree p d hp), hlow⟩

end Hindman168

