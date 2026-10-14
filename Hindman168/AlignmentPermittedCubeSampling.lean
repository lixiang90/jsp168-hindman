import Hindman168.AlignmentCubeBoxCoordinates
import Hindman168.AlignmentActualClassCounts

namespace Hindman168
open Filter
open scoped Topology Classical

theorem alignment_permitted_cube_sampling_eventually
    {ι : Type*} [Fintype ι] {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (c C eps : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U : Option ι → ℝ,
      (∀ j, |L j| ≤ C * alignmentLocalLength F w i ∧
        |U j| ≤ C * alignmentLocalLength F w i ∧ c * alignmentLocalLength F w i ≤ U j - L j) →
      ∀ r : Option ι → ℤ,
      let R : ℤ := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let lower := fun j => alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉
      let upper := fun j => alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉
      let residue := fun j => alignmentCubeCoordinate (F.modulus w) t p Y j (r j)
      let q : ℕ := d * alignmentNaturalBlockProduct x T
      (alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d).Nonempty ∧
      (alignmentBoxClass lower upper residue q).Nonempty ∧
      (∀ j, |((alignmentIntervalClass (lower j) (upper j) q (residue j)).card : ℝ) * q /
        ((upper j : ℝ) - lower j) - 1| ≤ eps) ∧
      ∀ f : (Option ι → ℤ) → ℂ,
        finiteComplexSetMean (alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d)
          (fun z => f (fun j => alignmentCubeCoordinate (F.modulus w) t p Y j (z j))) =
        finiteComplexSetMean (alignmentBoxClass lower upper residue q) f := by
  classical
  filter_upwards [alignment_actual_rounded_box_geometry_eventually (ι := ι) hF i T c C
      ⌈C + 1⌉₊ hc hC (Nat.le_ceil _),
    alignment_actual_class_count_eventually hF i T d hd (c / 2) eps (by positivity) heps]
    with w hw hcount x hx L U hbox r
  dsimp only
  have hg := hw x hx L U hbox
  dsimp only at hg
  have hj (j : Option ι) := hcount x hx
    (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) j ⌈L j⌉)
    (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) j ⌈U j⌉)
    (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T)
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
        (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) j (r j))
    (by simpa only [Int.cast_sub] using (hg j).2.2.1)
  have ht : (0 : ℤ) < alignmentNaturalBlockProduct x T := by
    exact_mod_cast (Finset.prod_pos hx : 0 < alignmentNaturalBlockProduct x T)
  have htarget := (alignmentBoxClass_nonempty_iff _ _ _ _).mpr (fun j => (hj j).1)
  have himg := alignment_cube_box_image (F.modulus w) (alignmentNaturalBlockProduct x T)
    (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
      (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ))
    d ht L U r
  rw [mul_comm _ (d : ℤ), ← Nat.cast_mul] at himg
  have hsource : (alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d).Nonempty := by
    have hne := himg.symm ▸ htarget
    exact Finset.image_nonempty.mp hne
  refine ⟨hsource, htarget, fun j => (hj j).2, ?_⟩
  intro f
  have hm := alignment_cube_box_mean (F.modulus w) (alignmentNaturalBlockProduct x T)
    (alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w))
      (F.modulus w) (x i)) ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ))
    d ht L U r f
  simpa only [Nat.cast_mul, mul_comm (d : ℤ)] using hm

end Hindman168
