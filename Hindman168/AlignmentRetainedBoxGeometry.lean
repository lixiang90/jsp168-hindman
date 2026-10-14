import Hindman168.AlignmentRetainedEndpointBounds
import Hindman168.AlignmentRetainedScaleGrowth

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_retained_step_small_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ (x : Fin n → ℕ) (q : ℕ), 0 < q → q ≤ F.auxiliary w i.val →
      (d : ℝ) * q ≤ eps * alignmentCubeScale F w i T x := by
  filter_upwards [alignment_retained_scale_eventually hF i T d hd 0 heps] with w hw x q hq hqV
  have h := hw x q 0 hq hqV (Nat.zero_le _)
  simp only [pow_zero] at h
  have hp : (0 : ℝ) < (d : ℝ) * q := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hp] at h
  simpa only [one_mul] using h

theorem alignment_retained_box_geometry_eventually
    {ι : Type*} {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (c B C : ℝ) (hc : 0 < c) :
    ∀ᶠ w in atTop, ∀ (x : Fin n → ℕ) (q : ℕ), 0 < q → q ≤ F.auxiliary w i.val →
      ∀ L U a : ι → ℤ,
      (∀ j, 0 ≤ a j ∧ a j < (d : ℤ) * q) →
      (∀ j, |(L j : ℝ)| ≤ B * alignmentCubeScale F w i T x ∧
        |(U j : ℝ)| ≤ B * alignmentCubeScale F w i T x ∧
        c * alignmentCubeScale F w i T x ≤ (U j : ℝ) - L j ∧
        (U j : ℝ) - L j ≤ C * alignmentCubeScale F w i T x) →
      let S := alignmentCubeScale F w i T x / ((d : ℝ) * q)
      ∀ j, |(alignmentRetainedEndpoint (L j) ((d : ℤ) * q) (a j) : ℝ)| ≤ (B + 1) * S ∧
        |(alignmentRetainedEndpoint (U j) ((d : ℤ) * q) (a j) : ℝ)| ≤ (B + 1) * S ∧
        (c / 2) * S ≤ (alignmentRetainedEndpoint (U j) ((d : ℤ) * q) (a j) : ℝ) -
          alignmentRetainedEndpoint (L j) ((d : ℤ) * q) (a j) ∧
        (alignmentRetainedEndpoint (U j) ((d : ℤ) * q) (a j) : ℝ) -
          alignmentRetainedEndpoint (L j) ((d : ℤ) * q) (a j) ≤ (C + 1) * S := by
  filter_upwards [alignment_retained_step_small_eventually hF i T d hd (eps := 1) zero_lt_one,
    alignment_retained_step_small_eventually hF i T d hd (eps := c / 2) (by positivity)]
    with w h1 hc2 x q hq hqV L U a ha hbox
  have hp : (0 : ℤ) < (d : ℤ) * q := by positivity
  have hz : (((d : ℤ) * q : ℤ) : ℝ) ≤ alignmentCubeScale F w i T x := by
    simpa only [Int.cast_mul, Int.cast_natCast, one_mul] using h1 x q hq hqV
  have hsmall : (((d : ℤ) * q : ℤ) : ℝ) ≤ (c / 2) * alignmentCubeScale F w i T x := by
    simpa only [Int.cast_mul, Int.cast_natCast] using hc2 x q hq hqV
  dsimp only
  intro j
  have hl := alignmentRetainedEndpoint_location (L j) ((d : ℤ) * q) (a j)
    (alignmentCubeScale F w i T x) B hp (ha j).1 (ha j).2 (hbox j).1 hz
  have hu := alignmentRetainedEndpoint_location (U j) ((d : ℤ) * q) (a j)
    (alignmentCubeScale F w i T x) B hp (ha j).1 (ha j).2 (hbox j).2.1 hz
  have hs := alignmentRetainedEndpoint_sides (L j) (U j) ((d : ℤ) * q) (a j)
    (alignmentCubeScale F w i T x) c C hp (hbox j).2.2.1 (hbox j).2.2.2 hsmall hz
  simpa only [Int.cast_mul, Int.cast_natCast] using And.intro hl (And.intro hu hs)

end Hindman168
