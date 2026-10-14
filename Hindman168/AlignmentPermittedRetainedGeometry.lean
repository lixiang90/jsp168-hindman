import Hindman168.AlignmentRetainedBoxGeometry
import Hindman168.AlignmentCubeBoxCoordinates

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_permitted_retained_geometry_eventually
    {ι : Type*} {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C + 1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) →
      (∀ j, j < i → x j ≤ F.cutoff w j.val ^ 2) →
      ∀ L U : Option ι → ℝ,
      (∀ j, |L j| ≤ C * alignmentLocalLength F w i ∧
        |U j| ≤ C * alignmentLocalLength F w i ∧ c * alignmentLocalLength F w i ≤ U j - L j) →
      ∀ V : Finset (Fin n), V ⊆ T → ∀ a : Option ι → ℤ,
      (∀ j, 0 ≤ a j ∧ a j < (d : ℤ) * alignmentNaturalBlockProduct x V) →
      let R : ℤ := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let step : ℤ := (d : ℤ) * alignmentNaturalBlockProduct x V
      let S := alignmentCubeScale F w i T x / (step : ℝ)
      let lower := fun j => alignmentRetainedEndpoint
        (alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉) step (a j)
      let upper := fun j => alignmentRetainedEndpoint
        (alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉) step (a j)
      ∀ j, |(lower j : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 3) * S ∧
        |(upper j : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 3) * S ∧
        (c / 4) * S ≤ (upper j : ℝ) - lower j ∧
        (upper j : ℝ) - lower j ≤ ((2 : ℝ) ^ T.card * (2 * C + 1) + 1) * S := by
  filter_upwards [alignment_actual_rounded_box_geometry_eventually (ι := ι) hF i T c C K hc hC hK,
    alignment_retained_box_geometry_eventually (ι := Option ι) hF i T d hd
      (c / 2) ((2 : ℝ) ^ T.card * (K + 1) + 2) ((2 : ℝ) ^ T.card * (2 * C + 1))
      (by positivity)] with w hg hr x hx hcut L U hbox V hV a ha
  have hq : 0 < alignmentNaturalBlockProduct x V :=
    Finset.prod_pos (fun j hj => hx j (hV hj))
  have hqV := alignment_earlier_block_product_bound hF w i x hcut V
    (fun j hj => hT j (hV hj))
  have hgeom := hg x hx L U hbox
  dsimp only at hgeom ⊢
  have h := hr x (alignmentNaturalBlockProduct x V) hq hqV
    (fun j => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) j ⌈L j⌉)
    (fun j => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) j ⌈U j⌉)
    a ha (by simpa only [Int.cast_sub] using hgeom)
  have he : c / 2 / 2 = c / 4 := by ring
  simpa only [Int.cast_mul, Int.cast_natCast, he, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using h

end Hindman168
