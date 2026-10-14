import Hindman168.AlignmentRoundedIntervals
import Hindman168.AlignmentCubeSideLengths

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_actual_rounded_interval_geometry_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C + 1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U : ℝ,
      |L| ≤ C * alignmentLocalLength F w i → |U| ≤ C * alignmentLocalLength F w i →
      c * alignmentLocalLength F w i ≤ U - L →
      let R : ℤ := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let Z := alignmentCubeScale F w i T x
      |(alignmentCubeBase (F.modulus w) t p Y ⌈L⌉ : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
      |(alignmentCubeBase (F.modulus w) t p Y ⌈U⌉ : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
      |((t * ⌈L⌉ : ℤ) : ℝ)| ≤ (2 : ℝ) ^ T.card * K * Z ∧
      |((t * ⌈U⌉ : ℤ) : ℝ)| ≤ (2 : ℝ) ^ T.card * K * Z ∧
      (c / 2) * Z ≤ ((t * (⌈U⌉ - ⌈L⌉) : ℤ) : ℝ) ∧
      ((t * (⌈U⌉ - ⌈L⌉) : ℤ) : ℝ) ≤ (2 : ℝ) ^ T.card * (2 * C + 1) * Z := by
  filter_upwards [alignment_rounded_intervals_eventually hF i c C hc,
    master_microcell_eventually_positive hF (fun _ => i)] with w hw hR x hx L U hL hU hlen
  dsimp only
  have hr := hw L U hL hU hlen
  have hkN := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (alignmentLocalLength F w i))
  have hellL := alignment_local_coordinate_width_bound F w i ⌈L⌉ K (hr.1.trans hkN)
  have hellU := alignment_local_coordinate_width_bound F w i ⌈U⌉ K (hr.2.1.trans hkN)
  have hp := alignment_actual_microcell_first_distance F w i (x i) hR
  refine ⟨alignment_actual_cube_base_fixed_multiple F w i T x hx hR _ _ K hp hellL,
    alignment_actual_cube_base_fixed_multiple F w i T x hx hR _ _ K hp hellU, ?_, ?_, ?_⟩
  · exact_mod_cast alignment_actual_cube_increment_bound F w i T x hx ⌈L⌉ K hellL
  · exact_mod_cast alignment_actual_cube_increment_bound F w i T x hx ⌈U⌉ K hellU
  · have hs := alignment_actual_cube_side_lengths F w i T x hx
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i))
      ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) ⌈L⌉ ⌈U⌉
      (c / 2) (2 * C + 1) (by positivity) (by positivity) hr.2.2.1 hr.2.2.2
    simpa only [alignmentCubeBase_interval_length] using hs

end Hindman168
