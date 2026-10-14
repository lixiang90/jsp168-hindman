import Hindman168.AlignmentRoundedCubeGeometry

namespace Hindman168
open Filter
open scoped Topology Classical

theorem alignmentBoxClass_nonempty_iff {ι : Type*} [Fintype ι]
    (L U r : ι → ℤ) (d : ℤ) :
    (alignmentBoxClass L U r d).Nonempty ↔ ∀ j, (alignmentIntervalClass (L j) (U j) d (r j)).Nonempty :=
  Fintype.piFinset_nonempty

def alignmentCubeCoordinate {ι : Type*} (M t p Y : ℤ) : Option ι → ℤ → ℤ
  | none, ell => alignmentCubeBase M t p Y ell
  | some _, ell => t * ell

theorem alignmentCubeCoordinate_affine {ι : Type*} (M t p Y : ℤ) (j : Option ι) (ell : ℤ) :
    alignmentCubeCoordinate M t p Y j ell = alignmentCubeCoordinate M t p Y j 0 + t * ell := by
  cases j <;> simp only [alignmentCubeCoordinate, alignmentCubeBase] <;> ring

theorem alignmentCubeCoordinate_length {ι : Type*} (M t p Y : ℤ) (j : Option ι) (L U : ℤ) :
    alignmentCubeCoordinate M t p Y j U - alignmentCubeCoordinate M t p Y j L = t * (U - L) := by
  rw [alignmentCubeCoordinate_affine M t p Y j U, alignmentCubeCoordinate_affine M t p Y j L]
  ring

theorem alignment_cube_box_mean {ι : Type*} [Fintype ι] (M t p Y d : ℤ) (ht : 0 < t)
    (L U : Option ι → ℝ) (r : Option ι → ℤ) (f : (Option ι → ℤ) → ℂ) :
    finiteComplexSetMean (alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d)
      (fun z => f (fun j => alignmentCubeCoordinate M t p Y j (z j))) =
      finiteComplexSetMean (alignmentBoxClass
        (fun j => alignmentCubeCoordinate M t p Y j ⌈L j⌉)
        (fun j => alignmentCubeCoordinate M t p Y j ⌈U j⌉)
        (fun j => alignmentCubeCoordinate M t p Y j (r j)) (t * d)) f := by
  simpa only [← alignmentCubeCoordinate_affine M t p Y] using
    alignment_affine_box_mean (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r
      (fun j => alignmentCubeCoordinate M t p Y j 0) t d ht f

theorem alignment_cube_box_image {ι : Type*} [Fintype ι] (M t p Y d : ℤ) (ht : 0 < t)
    (L U : Option ι → ℝ) (r : Option ι → ℤ) :
    (alignmentBoxClass (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r d).image
      (fun z => fun j => alignmentCubeCoordinate M t p Y j (z j)) =
      alignmentBoxClass (fun j => alignmentCubeCoordinate M t p Y j ⌈L j⌉)
        (fun j => alignmentCubeCoordinate M t p Y j ⌈U j⌉)
        (fun j => alignmentCubeCoordinate M t p Y j (r j)) (t * d) := by
  simpa only [← alignmentCubeCoordinate_affine M t p Y] using
    alignment_affine_box_image (fun j => ⌈L j⌉) (fun j => ⌈U j⌉) r
      (fun j => alignmentCubeCoordinate M t p Y j 0) t d ht

theorem alignment_actual_rounded_box_geometry_eventually
    {ι : Type*} {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C + 1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U : Option ι → ℝ,
      (∀ j, |L j| ≤ C * alignmentLocalLength F w i ∧
        |U j| ≤ C * alignmentLocalLength F w i ∧ c * alignmentLocalLength F w i ≤ U j - L j) →
      let R : ℤ := alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let Z := alignmentCubeScale F w i T x
      ∀ j, |(alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℝ)| ≤
          ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
        |(alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ : ℝ)| ≤
          ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
        (c / 2) * Z ≤ ((alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ -
          alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℤ) : ℝ) ∧
        ((alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ -
          alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℤ) : ℝ) ≤
            (2 : ℝ) ^ T.card * (2 * C + 1) * Z := by
  filter_upwards [alignment_actual_rounded_interval_geometry_eventually hF i T c C K hc hC hK]
    with w hw x hx L U hbox
  dsimp only
  intro j
  have hj := hw x hx (L j) (U j) (hbox j).1 (hbox j).2.1 (hbox j).2.2
  dsimp only at hj
  rw [alignmentCubeCoordinate_length]
  refine ⟨?_, ?_, hj.2.2.2.2⟩
  · cases j with
    | none => exact hj.1
    | some j =>
      apply hj.2.2.1.trans
      have hz : 0 ≤ alignmentCubeScale F w i T x := by
        unfold alignmentCubeScale alignmentShortBinVolume
        positivity
      apply mul_le_mul_of_nonneg_right _ hz
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ T.card by positivity]
  · cases j with
    | none => exact hj.2.1
    | some j =>
      apply hj.2.2.2.1.trans
      have hz : 0 ≤ alignmentCubeScale F w i T x := by
        unfold alignmentCubeScale alignmentShortBinVolume
        positivity
      apply mul_le_mul_of_nonneg_right _ hz
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ T.card by positivity]

end Hindman168
