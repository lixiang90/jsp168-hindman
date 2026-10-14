import Hindman168.SelectedAlignmentSourceArithmetic
import Hindman168.SelectedPrincipalMicrocellBounds
import Hindman168.AlignmentProgressionMicrocellBounds
import Hindman168.AlignmentArrayIntervalStability

/-! Actual mapped-letter displacement is negligible on the padding-gap
microcell. Bounds are requested only for the selected earlier coordinates;
there is no growth assertion involving unused coordinates below the raw pivot. -/
namespace Hindman168
open Filter
open scoped Topology Classical

theorem selected_alignment_microcell_polynomial_small
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n)
    (p : ℕ) (C : ℝ) :
    ∀ᶠ w in atTop, C * (selectedPrincipalAuxiliary F e w i : ℝ)^p ≤
      selectedPrincipalMicrocellWidth F e w i := by
  have hb := (selected_principal_microcell_growth hF e i).1.eventually_bound
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) p (show 0 < max C 1 by positivity)
  filter_upwards [hb] with w hw
  exact (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)).trans hw

/-- Every fixed selected stored-slot family fits inside the true microcell. -/
theorem selected_alignment_slot_uniform_margin
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀)
    (V : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ stored ∈ V, ∀ x : Fin M → ℕ,
      (∀ j, Nat.Coprime (x j) (primorial w)) →
      |alignmentIntegerSlotShift
        (fun p => alignmentPairResidue q₀ w (F.modulus w) p x)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)| ≤
          (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
  apply (eventually_all_finset V).mpr
  intro stored _
  filter_upwards [selected_alignment_microcell_polynomial_small hF e i 2
    (alignmentIntegerSlotWeight stored : ℝ), eventually_ge_atTop (q₀+1)] with w hw hqw
  intro x hx
  rw [selected_alignment_slot_shift]
  have hb := (selected_principal_actual_slot_shift_bound hF e heM hq hqw x hx stored).2
  have hm : (F.modulus w : ℕ) ≤ selectedPrincipalAuxiliary F e w i := by
    unfold selectedPrincipalAuxiliary; omega
  have hweight := alignmentIntegerSlotWeight_nonneg stored
  have hbound : |alignmentIntegerSlotShift
      (fun p => alignmentPairResidue q₀ w (F.modulus w) (p.map (principalAlignmentEmbedding e heM)) x)
      stored| ≤ (selectedPrincipalAuxiliary F e w i : ℤ)^2 * alignmentIntegerSlotWeight stored := by
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hweight
    exact_mod_cast Nat.pow_le_pow_left hm 2
  have hsmall : (selectedPrincipalAuxiliary F e w i : ℤ)^2 * alignmentIntegerSlotWeight stored ≤
      (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
    have hh : (selectedPrincipalAuxiliary F e w i : ℝ)^2 * (alignmentIntegerSlotWeight stored : ℝ) ≤
        selectedPrincipalMicrocellWidth F e w i := by simpa only [mul_comm] using hw
    exact_mod_cast hh
  exact hbound.trans hsmall

/-- This uses actual canonical residues and actual progression shifts. -/
theorem selected_alignment_progression_uniform_margin
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀)
    (U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ query ∈ U, ∀ x : Fin M → ℕ,
      (∀ j, Nat.Coprime (x j) (primorial w)) →
      (∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      ∀ T : Finset (Fin n),
      |(F.modulus w : ℤ) * alignmentIntegerArrayProgression
        (fun p => alignmentPairProgression q₀ w (F.modulus w) p x)
        (T.image (principalAlignmentEmbedding e heM))
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query)| ≤
          (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
  apply (eventually_all_finset U).mpr
  intro query _
  filter_upwards [selected_alignment_microcell_polynomial_small hF e i 3
    (2 * (alignmentIntegerSlotWeight query : ℝ)), eventually_ge_atTop (q₀+1)] with w hw hqw
  intro x hx hcut T
  rw [selected_alignment_array_progression]
  have hb := alignmentIntegerArrayProgression_scaled_bound (F.modulus w)
    (fun p => alignmentPairProgression q₀ w (F.modulus w) (p.map (principalAlignmentEmbedding e heM)) x)
    T query (L := 2 * (selectedPrincipalAuxiliary F e w i : ℤ)^3) (by positivity)
    (fun p => selected_principal_actual_progression_bound hF e heM hq hqw p x hx hcut)
  have hsmall : (2 * (selectedPrincipalAuxiliary F e w i : ℤ)^3) * alignmentIntegerSlotWeight query ≤
      (selectedPrincipalMicrocellWidth F e w i : ℤ) := by
    have hh : (2 * (selectedPrincipalAuxiliary F e w i : ℝ)^3) * (alignmentIntegerSlotWeight query : ℝ) ≤
        selectedPrincipalMicrocellWidth F e w i := by nlinarith [hw]
    exact_mod_cast hh
  exact hb.trans hsmall

/-- The original ambient integer array stays in the observer's PADDING
interval throughout a bounded multiple of the actual microcell. -/
theorem selected_alignment_array_interval_stable
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ stored ∈ V, ∀ query ∈ U, ∀ x : Fin M → ℕ,
      (∀ j, Nat.Coprime (x j) (primorial w)) →
      (∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      ∀ T : Finset (Fin n), (∀ k ∈ T, k < i) → ∀ p p₀ : ℤ,
      |p-p₀| ≤ (C * selectedPrincipalMicrocellWidth F e w i : ℕ) →
      intervalInteriorRoot (F.gap w (energyPadding e i))
        ((C+2) * F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i)
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) : ℤ) * p₀) →
      alignmentIntegerArrayArgument x (F.modulus w)
        (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (fun a => alignmentPairProgression q₀ w (F.modulus w) a x)
        (T.image (principalAlignmentEmbedding e heM)) p
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query) /
          (F.gap w (energyPadding e i) : ℤ) =
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) : ℤ) * p₀) /
          (F.gap w (energyPadding e i) : ℤ) := by
  filter_upwards [selected_alignment_slot_uniform_margin hF e heM i q₀ hq V,
    selected_alignment_progression_uniform_margin hF e heM i q₀ hq U] with w hs hu
  intro stored hstored query hquery x hx hcut T hT p p₀ hp hinterior
  let R := selectedPrincipalMicrocellWidth F e w i
  let t := alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM))
  have ht : t ≤ F.auxiliary w (energyPadding e i) := by
    rw [show t = principalSubsetProduct T (fun k => x (principalAlignmentEmbedding e heM k)) from
      alignment_natural_block_product_image _ _ _]
    exact (selected_principal_earlier_product_bound hF e w i _ hcut T hT).trans
      (hF.selected_auxiliary_le_padding e w i)
  have ha := F.auxiliary_ge_two w (energyPadding e i)
  have hmargin : t * (C*R+R) + R ≤ (C+2) * F.auxiliary w (energyPadding e i) * R := by
    calc
      _ ≤ F.auxiliary w (energyPadding e i) * (C*R+R) +
          F.auxiliary w (energyPadding e i) * R :=
        Nat.add_le_add (Nat.mul_le_mul_right _ ht)
          (by simpa using Nat.mul_le_mul_right R (show 1 ≤ F.auxiliary w (energyPadding e i) by omega))
      _ = _ := by ring
  have hi : intervalInteriorRoot (F.gap w (energyPadding e i)) (t * (C*R+R) + R)
      ((t : ℤ) * p₀) := by
    have hm : ((t * (C*R+R) + R : ℕ) : ℤ) ≤
        ((C+2) * F.auxiliary w (energyPadding e i) * R : ℕ) := by exact_mod_cast hmargin
    exact ⟨hm.trans hinterior.1, lt_of_le_of_lt (add_le_add le_rfl hm) hinterior.2⟩
  exact alignmentIntegerArrayArgument_interval_stable x (F.modulus w) _ _ _ p p₀ _ _
    (F.gap w (energyPadding e i)) (C*R) R R (hF.gap_positive w _) hp
    (hs stored hstored x hx) (hu query hquery x hx hcut T) hi

end Hindman168
