import Hindman168.SelectedAlignmentNativeWindow
import Hindman168.AlignmentActualOriginalResidualGeometry

/-! Original rounded and retained residual boxes at a padding gap and a
separate raw pivot. Growth is taken at the genuine padding index. -/
namespace Hindman168
open Filter
open scoped Topology

@[simp] theorem alignmentGeometryWithGap_length {N : ℕ} (F : MasterParameterFamily)
    (i gap : Fin N) (w : ℕ) :
    alignmentLocalLength (alignmentGeometryWithGap F i gap) w i =
      alignmentLocalLength F w gap := by
  simp only [alignmentLocalLength, alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus]

theorem selected_alignment_actual_rounded_interval_geometry_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i gap : Fin n) (T : Finset (Fin n)) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C + 1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U : ℝ,
      |L| ≤ C * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i → |U| ≤ C * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i →
      c * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ≤ U - L →
      let R : ℤ := alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let Z := alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x
      |(alignmentCubeBase (F.modulus w) t p Y ⌈L⌉ : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
      |(alignmentCubeBase (F.modulus w) t p Y ⌈U⌉ : ℝ)| ≤ ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
      |((t * ⌈L⌉ : ℤ) : ℝ)| ≤ (2 : ℝ) ^ T.card * K * Z ∧
      |((t * ⌈U⌉ : ℤ) : ℝ)| ≤ (2 : ℝ) ^ T.card * K * Z ∧
      (c / 2) * Z ≤ ((t * (⌈U⌉ - ⌈L⌉) : ℤ) : ℝ) ∧
      ((t * (⌈U⌉ - ⌈L⌉) : ℤ) : ℝ) ≤ (2 : ℝ) ^ T.card * (2 * C + 1) * Z := by
  filter_upwards [alignment_rounded_intervals_eventually hF gap c C hc,
    master_microcell_eventually_positive hF (fun _ => gap)] with w hw hR x hx L U hL hU hlen
  have hR : 0 < alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w) := by simpa only [alignmentGeometryWithGap_gap] using hR
  simp only [alignmentGeometryWithGap_length] at hL hU hlen
  dsimp only
  have hr := hw L U hL hU hlen
  simp only [← alignmentGeometryWithGap_length F i gap w] at hr
  have hkN := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (alignmentLocalLength (alignmentGeometryWithGap F i gap) w i))
  have hellL := alignment_local_coordinate_width_bound (alignmentGeometryWithGap F i gap) w i ⌈L⌉ K (hr.1.trans hkN)
  have hellU := alignment_local_coordinate_width_bound (alignmentGeometryWithGap F i gap) w i ⌈U⌉ K (hr.2.1.trans hkN)
  have hp := alignment_actual_microcell_first_distance (alignmentGeometryWithGap F i gap) w i (x i) hR
  refine ⟨alignment_actual_cube_base_fixed_multiple (alignmentGeometryWithGap F i gap) w i T x hx hR _ _ K hp hellL,
    alignment_actual_cube_base_fixed_multiple (alignmentGeometryWithGap F i gap) w i T x hx hR _ _ K hp hellU, ?_, ?_, ?_⟩
  · exact_mod_cast alignment_actual_cube_increment_bound (alignmentGeometryWithGap F i gap) w i T x hx ⌈L⌉ K hellL
  · exact_mod_cast alignment_actual_cube_increment_bound (alignmentGeometryWithGap F i gap) w i T x hx ⌈U⌉ K hellU
  · have hs := alignment_actual_cube_side_lengths (alignmentGeometryWithGap F i gap) w i T x hx
      (alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w))
        (F.modulus w) (x i))
      ((alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T x : ℤ) / (F.modulus w : ℤ)) ⌈L⌉ ⌈U⌉
      (c / 2) (2 * C + 1) (by positivity) (by positivity)
      (by simpa only [alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hr.2.2.1)
      (by simpa only [alignmentGeometryWithGap_gap, alignmentGeometryWithGap_modulus] using hr.2.2.2)
    simpa only [alignmentCubeBase_interval_length] using hs


theorem selected_alignment_actual_rounded_box_geometry_eventually
    {ι : Type*} {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i gap : Fin n) (T : Finset (Fin n)) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C + 1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U : Option ι → ℝ,
      (∀ j, |L j| ≤ C * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧
        |U j| ≤ C * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧ c * alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ≤ U j - L j) →
      let R : ℤ := alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w)
      let p := alignmentMicrocellFirst R (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T x : ℤ) / (F.modulus w : ℤ)
      let t : ℤ := alignmentNaturalBlockProduct x T
      let Z := alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x
      ∀ j, |(alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℝ)| ≤
          ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
        |(alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ : ℝ)| ≤
          ((2 : ℝ) ^ T.card * (K + 1) + 2) * Z ∧
        (c / 2) * Z ≤ ((alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ -
          alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℤ) : ℝ) ∧
        ((alignmentCubeCoordinate (F.modulus w) t p Y j ⌈U j⌉ -
          alignmentCubeCoordinate (F.modulus w) t p Y j ⌈L j⌉ : ℤ) : ℝ) ≤
            (2 : ℝ) ^ T.card * (2 * C + 1) * Z := by
  filter_upwards [selected_alignment_actual_rounded_interval_geometry_eventually hF i gap T c C K hc hC hK]
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
      have hz : 0 ≤ alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x := by
        unfold alignmentCubeScale alignmentShortBinVolume
        positivity
      apply mul_le_mul_of_nonneg_right _ hz
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ T.card by positivity]
  · cases j with
    | none => exact hj.2.1
    | some j =>
      apply hj.2.2.2.1.trans
      have hz : 0 ≤ alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x := by
        unfold alignmentCubeScale alignmentShortBinVolume
        positivity
      apply mul_le_mul_of_nonneg_right _ hz
      nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ T.card by positivity]


theorem selected_alignment_actual_original_residual_geometry_eventually {κ : Type*}
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (i gap : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ)) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      ∀ L H : Option κ → ℝ,
      (∀ j, |L j| ≤ C*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧
        |H j| ≤ C*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ∧ c*alignmentLocalLength (alignmentGeometryWithGap F i gap) w i ≤ H j-L j) →
      ∀ U : Finset (Fin N), U ⊆ T → ∀ a : Option κ → ℤ,
      (∀ j, 0 ≤ a j ∧ a j < (d*alignmentNaturalBlockProduct x U : ℕ)) →
      let q : ℕ := d*alignmentNaturalBlockProduct x U
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth ((alignmentGeometryWithGap F i gap).gap w i.val) (F.modulus w)) (F.modulus w) (x i)
      let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i gap) w i T x : ℤ)/(F.modulus w : ℤ)
      let lo := fun j => (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T) p Y j ⌈L j⌉ : ℝ)
      let hi := fun j => (alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct x T) p Y j ⌈H j⌉ : ℝ)
      let Z := alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x/(q : ℝ)
      ∀ j, (c/2)*Z ≤ (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ∧
        (hi j-(a j : ℝ))/(q : ℝ)-(lo j-(a j : ℝ))/(q : ℝ) ≤ alignmentOriginalResidualUpper T.card K C*Z ∧
        |(lo j-(a j : ℝ))/(q : ℝ)| ≤ alignmentOriginalResidualUpper T.card K C*Z ∧
        |(hi j-(a j : ℝ))/(q : ℝ)| ≤ alignmentOriginalResidualUpper T.card K C*Z := by
  filter_upwards [selected_alignment_actual_rounded_box_geometry_eventually (ι := κ) hF i gap T c C K hc hC hK,
    alignment_retained_scale_eventually hF gap T d hd 0 (eps := 1) (by norm_num),
    alignmentGlobalRawMass_geometry hF] with w hg hs hraw
  intro x hx L H hbox U hU a ha
  dsimp only
  have hpos := fun j (_hj : j ∈ T) => alignmentGlobalRawMass_support_positive hF w x hx j
  have hret : 0 < alignmentNaturalBlockProduct x U := Finset.prod_pos (fun j hj => hpos j (hU hj))
  have hretAux := alignment_earlier_block_product_bound hF w gap x (fun j _ => hraw.2.2 x hx j) U
    (fun j hj => hT j (hU hj))
  have hscale := hs x (alignmentNaturalBlockProduct x U) 0 hret hretAux (Nat.zero_le _)
  simp only [pow_zero,one_mul] at hscale
  rw [← alignmentGeometryWithGap_cubeScale F i gap w T x] at hscale
  have hqR : (0 : ℝ) < (d : ℝ)*alignmentNaturalBlockProduct x U := by positivity
  have hZ : ((d*alignmentNaturalBlockProduct x U : ℕ) : ℝ) ≤ alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x := by
    have hh := (le_div_iff₀ hqR).mp hscale
    simpa only [one_mul,Nat.cast_mul] using hh
  have hgeom := hg x hpos L H hbox
  dsimp only at hgeom
  have hh := original_integer_residual_box_geometry _ _ a (d*alignmentNaturalBlockProduct x U)
    (Nat.mul_pos hd hret) (alignmentCubeScale (alignmentGeometryWithGap F i gap) w i T x) (c/2)
    ((2 : ℝ)^T.card*((K : ℝ)+1)+2) ((2 : ℝ)^T.card*(2*C+1)) hZ ha
    (by simpa only [Int.cast_sub] using hgeom)
  simpa only [alignmentOriginalResidualUpper,add_assoc,show (2 : ℝ)+1=3 by norm_num] using hh


end Hindman168
