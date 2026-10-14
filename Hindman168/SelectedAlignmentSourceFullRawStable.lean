import Hindman168.SelectedAlignmentSourceFrozenReadings

/-! Stability for the ACTUAL full raw anchor. Unselected outside coordinates
remain their sampled values. This is the nonempty-fiber interface used by
full raw extraction, separate from the one-filled selected source adapter. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical BigOperators

noncomputable def selectedAlignmentFullFrozenLabel {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w : ℕ)
    (T : Finset (Fin n)) (x : Fin M → ℕ) (stored : AlignmentAddingPair n i → ℤ) : ℤ × ℤ :=
  (((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) * x (principalAlignmentEmbedding e heM i) : ℕ):ℤ) / (F.gap w (energyPadding e i):ℤ),
    alignmentPivotArrayResidue x (T.image (principalAlignmentEmbedding e heM)) (F.modulus w) (x (principalAlignmentEmbedding e heM i))
      (alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)))

noncomputable def selectedAlignmentFullExposureArrayStable {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ)) (x : Fin M → ℕ) : Prop :=
  ∀ y : Fin M → ℕ, (∀ j, Nat.Coprime (y j) (primorial w)) →
    (∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
    alignmentShortExposureKey
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
      (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM))
      x =
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
      selectedAlignmentFullFrozenLabel F e heM i q₀ w T x stored

theorem selected_alignment_full_boundary_implies_exposure_stable
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support,
      intervalInteriorRoot (F.gap w (energyPadding e i))
        ((C+3) * F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i)
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i):ℕ):ℤ) →
      selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x := by
  filter_upwards [selected_alignment_exposure_canonical_piece hF e heM i q₀ hq C V U,
    alignmentGlobalRawMass_geometry hF] with w hw hg
  intro x hx hinterior y hyc hy hkey stored hstored query hquery p hp hdist
  exact hw T hT x y (fun k _ => hg.2.2 x hx (principalAlignmentEmbedding e heM k))
    (fun k _ => alignmentGlobalRawMass_support_positive hF w x hx (principalAlignmentEmbedding e heM k))
    hy (alignmentGlobalRawMass_support_coprime F w x hx) hyc hkey hinterior
    stored hstored query hquery p hp hdist

/-- The genuine full raw extraction loses asymptotically no mass. -/
theorem selected_alignment_full_exposure_failure_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (T : Finset (Fin n)) (hT : ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => ¬ selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (selected_alignment_raw_block_boundary_tendsto hF e heM i T hT (C+3))
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF,
      selected_alignment_full_boundary_implies_exposure_stable hF e heM i q₀ hq C T hT V U] with w hw hs
    rw [event_eq_sum _ _ (Finset.Subset.refl _), event_eq_sum _ _ (Finset.Subset.refl _)]
    apply Finset.sum_le_sum
    intro x hx
    by_cases hb : ¬ selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x
    · have hn := mt (hs x hx) hb
      simp only [selectedPrincipalMicrocellWidth, alignment_natural_block_product_image] at hn
      change ¬ intervalInteriorRoot _ _
        ((principalSubsetProduct T (fun k => x (selectedPrincipalIndex e heM k)) *
          x (selectedPrincipalIndex e heM i):ℕ):ℤ) at hn
      rw [if_pos hb, if_pos hn]
    · rw [if_neg hb]
      split_ifs <;> first | exact hw.1 x | exact le_rfl

/-- One common full-raw good event handles every finite stored target. -/
theorem selected_alignment_full_finite_exposure_failure_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (S : Finset (Finset (Fin n))) (hS : ∀ T ∈ S, ∀ k ∈ T, k < i)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) M)
      (fun x => ∃ T ∈ S, ¬ selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x)) atTop (𝓝 0) := by
  have hh := tendsto_finsetSum S (fun T hT =>
    selected_alignment_full_exposure_failure_tendsto hF e heM i q₀ hq C T (hS T hT) V U)
  simp only [Finset.sum_const_zero] at hh
  apply squeeze_zero' _ _ hh
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_union_bound _ S _ hw.1

end Hindman168
