import Hindman168.AlignmentLocalLength
import Hindman168.AlignmentCeilBoxes

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_actual_microcell_progression {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (p ell : ℤ) :
    let R : ℤ := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
    (p / R) * R ≤ alignmentMicrocellFirst R (F.modulus w) p + (F.modulus w : ℤ) * ell ∧
      alignmentMicrocellFirst R (F.modulus w) p + (F.modulus w : ℤ) * ell < (p / R) * R + R ↔
      0 ≤ ell ∧ ell < alignmentLocalLength F w i := by
  dsimp only
  have h := alignment_residue_progression_interval
    ((p / (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ)) *
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ))
    (F.modulus w) (alignmentLocalLength F w i) p ell (by exact_mod_cast (F.modulus w).pos)
  have he : (F.modulus w : ℤ) * alignmentLocalLength F w i =
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) := by
    exact_mod_cast alignmentLocalLength_exact F w i
  rw [he] at h
  exact h

theorem alignment_rounded_intervals_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ w in atTop, ∀ L U : ℝ,
      |L| ≤ C * alignmentLocalLength F w i → |U| ≤ C * alignmentLocalLength F w i →
      c * alignmentLocalLength F w i ≤ U - L →
      |(⌈L⌉ : ℝ)| ≤ (C + 1) * alignmentLocalLength F w i ∧
      |(⌈U⌉ : ℝ)| ≤ (C + 1) * alignmentLocalLength F w i ∧
      (c / 2) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) ≤
        (F.modulus w : ℝ) * ((⌈U⌉ : ℝ) - (⌈L⌉ : ℝ)) ∧
      (F.modulus w : ℝ) * ((⌈U⌉ : ℝ) - (⌈L⌉ : ℝ)) ≤
        (2 * C + 1) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) := by
  filter_upwards [alignmentLocalLength_eventually_large hF i (max 1 (2 / c))]
    with w hw L U hL hU hlen
  have hN := (le_max_left (1 : ℝ) (2 / c)).trans hw
  have hlarge : 2 ≤ c * (alignmentLocalLength F w i : ℝ) := by
    have h := (div_le_iff₀ hc).mp ((le_max_right (1 : ℝ) (2 / c)).trans hw)
    nlinarith
  have hs := alignment_ceil_side_bounds L U (alignmentLocalLength F w i) c C hN hlarge hlen
    (by linarith [(abs_le.mp hL).1]) (abs_le.mp hU).2
  have hMN : (F.modulus w : ℝ) * alignmentLocalLength F w i =
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) := by
    exact_mod_cast alignmentLocalLength_exact F w i
  have hm : (0 : ℝ) ≤ F.modulus w := by positivity
  refine ⟨alignment_ceil_endpoint_bound L _ C hN hL,
    alignment_ceil_endpoint_bound U _ C hN hU, ?_, ?_⟩
  · calc
      _ = (F.modulus w : ℝ) * ((c / 2) * alignmentLocalLength F w i) := by rw [← hMN]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs.1 hm
  · calc
      _ ≤ (F.modulus w : ℝ) * ((2 * C + 1) * alignmentLocalLength F w i) :=
        mul_le_mul_of_nonneg_left hs.2 hm
      _ = _ := by rw [← hMN]; ring

theorem alignment_local_coordinate_width_bound {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (ell : ℤ) (K : ℕ)
    (hell : |(ell : ℝ)| ≤ (K : ℝ) * alignmentLocalLength F w i) :
    |(F.modulus w : ℤ) * ell| ≤
      (K : ℤ) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℤ) := by
  have hMN : (F.modulus w : ℝ) * alignmentLocalLength F w i =
      (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) := by
    exact_mod_cast alignmentLocalLength_exact F w i
  have h : |(F.modulus w : ℝ) * (ell : ℝ)| ≤
      (K : ℝ) * (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℝ) := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ F.modulus w by positivity)]
    calc
      _ ≤ (F.modulus w : ℝ) * ((K : ℝ) * alignmentLocalLength F w i) :=
        mul_le_mul_of_nonneg_left hell (by positivity)
      _ = _ := by rw [← hMN]; ring
  exact_mod_cast h

end Hindman168
