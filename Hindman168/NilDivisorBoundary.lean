import Hindman168.NilBoundaryPeriod
import Hindman168.NilPeriodicHarmonic
import Hindman168.FiniteWeightedErrors
import Hindman168.HarmonicDilation

/-! A finite, uniform boundary bound for the original harmonic sample
with a fixed divisor draw. Coprimality and divisibility are encoded in
period W*σ, while the original normalizer is kept unchanged. -/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

noncomputable def divisorBoundaryTest (σ R H : ℕ) (y : ℤ) : ℝ :=
  if (σ : ℤ) ∣ y ∧ ¬ intervalInteriorRoot R H y then (σ : ℝ) else 0

theorem unitResidues_mem_mod (W σ n : ℕ) (hW : 0 < W) (hσ : 0 < σ) :
    n % (W * σ) ∈ unitResidues W σ 0 ↔ n.Coprime W ∧ σ ∣ n := by
  have hcop : (n % (W * σ)).Coprime W ↔ n.Coprime W := by
    change (n % (W * σ)).gcd W = 1 ↔ n.gcd W = 1
    rw [((Nat.mod_modEq n (W * σ)).of_mul_right σ).gcd_eq]
  have hmod : (n % (W * σ)) % σ = n % σ := Nat.mod_mod_of_dvd n (dvd_mul_left σ W)
  simp only [unitResidues, Finset.mem_filter, Finset.mem_range,
    Nat.mod_lt n (Nat.mul_pos hW hσ), true_and, hcop, hmod, Nat.dvd_iff_mod_eq_zero]

theorem integerMass_divisorBoundary_formula (X W σ R H : ℕ)
    (hW : 0 < W) (hσ : 0 < σ) (hR : 0 < R) :
    expectation (integerMass X W) (divisorBoundaryTest σ R H) =
      (σ : ℝ) * periodicResidueHarmonic X (X ^ 2 : ℕ) ((W * σ) * R)
        (jointBoundaryResidues R H (W * σ) (unitResidues W σ 0)) /
        harmonicNormalizer X W := by
  let U := jointBoundaryResidues R H (W * σ) (unitResidues W σ 0)
  have hm (n : ℕ) : n % ((W * σ) * R) ∈ U ↔
      n.Coprime W ∧ σ ∣ n ∧ ¬ intervalInteriorRoot R H (n : ℤ) := by
    rw [jointBoundaryResidues_mem_mod R H (W * σ) hR (Nat.mul_pos hW hσ),
      unitResidues_mem_mod W σ n hW hσ]
    exact and_assoc
  have hu (n : ℕ) (hn : n % ((W * σ) * R) ∈ U) : n.Coprime W := ((hm n).mp hn).1
  rw [integerMass, expectation_push]
  calc
    _ = expectation (rawMass X W) (fun n => if n % ((W * σ) * R) ∈ U then (σ : ℝ) else 0) := by
      apply expectation_congr_support
      intro n hn
      have hc : n.Coprime W := (Finset.mem_filter.mp
        (((intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset) hn)).2
      simp only [divisorBoundaryTest, Int.natCast_dvd_natCast]
      by_cases hd : σ ∣ n <;> by_cases hb : intervalInteriorRoot R H (n : ℤ) <;>
        simp [hm, hc, hd, hb]
    _ = _ := rawMass_periodic_test X W ((W * σ) * R) U σ hu

theorem harmonicNormalizer_boundary_lower {X W : ℕ} (hX : 2 ≤ X) (hW : 0 < W)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    0 < harmonicNormalizer X W ∧
      unitDensity W ≤ harmonicNormalizer X W ∧
      unitDensity W * Real.log X ≤ 2 * harmonicNormalizer X W := by
  have hD : 1 ≤ Real.log (X : ℝ) - (W : ℝ) / X := by linarith
  have hL : Real.log (X : ℝ) ≤ 2 * (Real.log (X : ℝ) - (W : ℝ) / X) := by linarith
  have hz := harmonicNormalizer_lower hX hW
  have hu := unitDensity_pos hW
  have ha := mul_le_mul_of_nonneg_left hD hu.le
  have hb := mul_le_mul_of_nonneg_left hL hu.le
  exact ⟨lt_of_lt_of_le hu (by nlinarith), by nlinarith, by nlinarith⟩

theorem integerMass_divisorBoundary_bound {X W σ R H d : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (hσ : 0 < σ) (hR : 0 < R)
    (hco : W.Coprime σ) (hH : H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W) (divisorBoundaryTest σ R H) ≤
      4 * (H : ℝ) / R + (4 + 8 * (d : ℝ)) * (W * σ : ℕ) / R +
        (W * σ : ℕ) * ((R : ℝ) + 1) / X := by
  let q := W * σ
  let U := unitResidues W σ 0
  let V := jointBoundaryResidues R H q U
  have hq : 0 < q := Nat.mul_pos hW hσ
  have hU : U ⊆ Finset.range q := Finset.filter_subset _ _
  have hV : V ⊆ Finset.range (q * R) := jointBoundaryResidues_subset R H q U
  have hcard : U.card = W.totient := unitResidues_card hW hσ hco hσ
  have hdim := jointBoundaryResidues_card_bound R H q d hR hq hH U hU
  have htotal := jointBoundaryResidues_card_total_bound R H q hq U hU
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hXX : (X : ℝ) < (X ^ 2 : ℕ) := by
    rw [Nat.cast_pow]
    have h2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hxratio : ((X ^ 2 : ℕ) : ℝ) / X = X := by rw [Nat.cast_pow]; field_simp
  have hh := (abs_le.mp (periodicResidueHarmonic_error hXR hXX
    (Nat.mul_pos hq hR) V hV)).2
  rw [hxratio] at hh
  have hlog0 : 0 ≤ Real.log (X : ℝ) := by linarith
  have hmain := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdim (Nat.cast_nonneg (q * R) : (0 : ℝ) ≤ ((q * R : ℕ) : ℝ))) hlog0
  have herr := div_le_div_of_nonneg_right htotal hXR.le
  have hnum := mul_le_mul_of_nonneg_left (by linarith :
    periodicResidueHarmonic X (X ^ 2 : ℕ) (q * R) V ≤
      ((U.card : ℝ) * (2 * (H : ℝ) + (q : ℝ) * (2 + 4 * d))) / (q * R : ℕ) *
        Real.log X + ((U.card : ℝ) * ((R : ℝ) + 1)) / X) hσR.le
  let a : ℝ := 2 * (H : ℝ) / R + (2 + 4 * (d : ℝ)) * (q : ℝ) / R
  let b : ℝ := (q : ℝ) * ((R : ℝ) + 1) / X
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have halg : (σ : ℝ) *
      (((U.card : ℝ) * (2 * (H : ℝ) + (q : ℝ) * (2 + 4 * d))) /
        (q * R : ℕ) * Real.log X + ((U.card : ℝ) * ((R : ℝ) + 1)) / X) =
      unitDensity W * Real.log X * a + unitDensity W * b := by
    dsimp [a, b]
    rw [hcard]
    dsimp [q, unitDensity]
    push_cast
    field_simp
  rw [halg] at hnum
  obtain ⟨hZ, hZ1, hZlog⟩ := harmonicNormalizer_boundary_lower hX hW hlog hWX
  have hm := add_le_add (mul_le_mul_of_nonneg_right hZlog ha)
    (mul_le_mul_of_nonneg_right hZ1 hb)
  have hbound : (σ : ℝ) * periodicResidueHarmonic X (X ^ 2 : ℕ) (q * R) V ≤
      (2 * a + b) * harmonicNormalizer X W := by nlinarith
  rw [integerMass_divisorBoundary_formula X W σ R H hW hσ hR]
  have hr := (div_le_iff₀ hZ).mpr hbound
  have he : 2 * a + b = 4 * (H : ℝ) / R + (4 + 8 * (d : ℝ)) * (W * σ : ℕ) / R +
      (W * σ : ℕ) * ((R : ℝ) + 1) / X := by dsimp [a, b, q]; ring
  exact hr.trans_eq he

theorem integerMass_divisorBoundary_uniform_bound {X W σ K R H d J : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (hσ : 0 < σ) (hσK : σ ≤ K)
    (hR : 0 < R) (hJ : 0 < J) (hco : W.Coprime σ) (hmargin : J * H ≤ d * R)
    (hlog : 2 ≤ Real.log (X : ℝ)) (hWX : (W : ℝ) / X ≤ 1) :
    expectation (integerMass X W) (divisorBoundaryTest σ R H) ≤
      4 * (d : ℝ) / J + (4 + 8 * (d : ℝ)) * (W * K : ℕ) / R +
        (W * K : ℕ) * ((R : ℝ) + 1) / X := by
  have hH : H ≤ d * R := (Nat.le_mul_of_pos_left H hJ).trans hmargin
  have hb := integerMass_divisorBoundary_bound hX hW hσ hR hco hH hlog hWX
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hfrac : (H : ℝ) / R ≤ (d : ℝ) / J := by
    apply (div_le_div_iff₀ hRR hJR).mpr
    have hm : (J : ℝ) * H ≤ (d : ℝ) * R := by exact_mod_cast hmargin
    nlinarith
  have hcap : (W * σ : ℕ) ≤ (W * K : ℕ) := Nat.mul_le_mul_left W hσK
  have hcapR : ((W * σ : ℕ) : ℝ) ≤ (W * K : ℕ) := by exact_mod_cast hcap
  have hfirst := mul_le_mul_of_nonneg_left hfrac (by norm_num : (0 : ℝ) ≤ 4)
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcapR (by positivity : 0 ≤ 4 + 8 * (d : ℝ))) hRR.le
  have hthird := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcapR (by positivity : 0 ≤ (R : ℝ) + 1)) hXR.le
  simp only [← mul_div_assoc] at hfirst
  nlinarith

end Hindman168
