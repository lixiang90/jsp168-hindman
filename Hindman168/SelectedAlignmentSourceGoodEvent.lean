import Hindman168.SelectedAlignmentSourceReadings
import Hindman168.SelectedAlignmentBoundaryRates

/-! The actual selected raw law loses asymptotically no mass when requiring
all tested points of an entire short-exposure fiber to have the frozen piece. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical BigOperators

noncomputable def selectedAlignmentFrozenLabel {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w : ℕ)
    (T : Finset (Fin n)) (x : Fin n → ℕ) (stored : AlignmentAddingPair n i → ℤ) : ℤ × ℤ :=
  let y := selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x
  (((principalSubsetProduct T x * x i : ℕ):ℤ) / (F.gap w (energyPadding e i):ℤ),
    alignmentPivotArrayResidue y (T.image (principalAlignmentEmbedding e heM)) (F.modulus w) (x i)
      (alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a y)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)))

noncomputable def selectedAlignmentExposureArrayStable {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ)) (x : Fin n → ℕ) : Prop :=
  ∀ y : Fin M → ℕ, (∀ j, Nat.Coprime (y j) (primorial w)) →
    (∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
    alignmentShortExposureKey
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
      (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM))
      (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) =
    alignmentShortExposureKey
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
      (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) y →
    ∀ stored ∈ V, ∀ query ∈ U, ∀ p : ℤ,
    Int.ModEq (F.modulus w:ℕ) p (y (principalAlignmentEmbedding e heM i)) →
    |p-y (principalAlignmentEmbedding e heM i)| ≤ (C*selectedPrincipalMicrocellWidth F e w i:ℕ) →
    intervalResiduePiece (F.gap w (energyPadding e i)) (F.modulus w)
      (alignmentIntegerArrayArgument y (F.modulus w)
        (fun a => alignmentPairResidue q₀ w (F.modulus w) a y)
        (fun a => alignmentPairProgression q₀ w (F.modulus w) a y)
        (T.image (principalAlignmentEmbedding e heM)) p
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query)) =
      selectedAlignmentFrozenLabel F e heM i q₀ w T x stored

theorem selected_alignment_raw_support_geometry
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (w : ℕ) (x : Fin n → ℕ) (hx : x ∈ (selectedPrincipalRawMass e F w).support) (k : Fin n) :
    0 < x k ∧ x k ≤ F.cutoff w (energyPrincipal e k)^2 ∧ Nat.Coprime (x k) (primorial w) := by
  have hne := Finsupp.mem_support_iff.mp hx
  rw [selectedPrincipalRawMass, piMass_apply] at hne
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k))
  have hw := Finset.mem_filter.mp (rawMass_support_window _ _ hs)
  exact ⟨(hF.cutoff_positive w _).trans_le (Finset.mem_Ico.mp hw.1).1,
    (Finset.mem_Ico.mp hw.1).2.le, hw.2⟩

/-- The good event is discharged by a concrete padding boundary test. -/
theorem selected_alignment_boundary_implies_exposure_stable
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ x ∈ (selectedPrincipalRawMass e F w).support,
      intervalInteriorRoot (F.gap w (energyPadding e i))
        ((C+3) * F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i)
        ((principalSubsetProduct T x * x i:ℕ):ℤ) →
      selectedAlignmentExposureArrayStable F e heM i q₀ w C T V U x := by
  filter_upwards [selected_alignment_exposure_canonical_piece hF e heM i q₀ hq C V U] with w hw
  intro x hx hinterior y hyc hy hkey stored hstored query hquery p hp hdist
  have hxg := selected_alignment_raw_support_geometry hF e w x hx
  have hh := hw T hT (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) y
    (by intro k hk; simpa only [selected_alignment_sample_extension_apply] using (hxg k).2.1)
    (by intro k hk; simpa only [selected_alignment_sample_extension_apply] using (hxg k).1)
    hy (selected_alignment_sample_extension_coprime _ x (primorial w) (fun k => (hxg k).2.2)) hyc hkey
    (by simpa only [selected_alignment_block_product, selected_alignment_sample_extension_apply] using hinterior)
    stored hstored query hquery p hp hdist
  simpa only [selectedAlignmentFrozenLabel, selected_alignment_block_product,
    selected_alignment_sample_extension_apply] using hh

/-- Genuine raw failure tends to zero, without an assumed stability law. -/
theorem selected_alignment_exposure_failure_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (selectedPrincipalRawMass e F w)
      (fun x => ¬ selectedAlignmentExposureArrayStable F e heM i q₀ w C T V U x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (selected_alignment_principal_raw_boundary_tendsto hF e heM i T hT (C+3))
  · filter_upwards [hF.selected_principal_raw_probability e heM] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [hF.selected_principal_raw_probability e heM,
      selected_alignment_boundary_implies_exposure_stable hF e heM i q₀ hq C T hT V U] with w hw hs
    rw [event_eq_sum _ _ (Finset.Subset.refl _), event_eq_sum _ _ (Finset.Subset.refl _)]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hb : ¬ selectedAlignmentExposureArrayStable F e heM i q₀ w C T V U x
    · have hn := mt (hs x hx) hb
      change ¬ intervalInteriorRoot _ _ _ at hn
      simp only [selectedPrincipalMicrocellWidth] at hn
      rw [if_pos hb, if_pos hn]
    · rw [if_neg hb]
      split_ifs <;> first | exact hw.1 x | exact le_rfl

/-- Any finite target catalogue has one common full-mass stability event. -/
theorem selected_alignment_finite_exposure_failure_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (selectedPrincipalRawMass e F w)
      (fun x => ∃ T ∈ S, ¬ selectedAlignmentExposureArrayStable F e heM i q₀ w C T V U x)) atTop (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun T hT =>
    selected_alignment_exposure_failure_tendsto hF e heM i q₀ hq C T (hS T hT) V U)
  simp only [Finset.sum_const_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [hF.selected_principal_raw_probability e heM] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [hF.selected_principal_raw_probability e heM] with w hw
    exact event_union_bound _ S _ hw.1

end Hindman168
