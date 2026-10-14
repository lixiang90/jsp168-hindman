import Hindman168.SelectedAlignmentCatalogueLetters
import Hindman168.SelectedAlignmentSourceExtension
import Hindman168.AlignmentJointRouteReadingsLift

/-! Selected route readings are actual ambient quotient evaluations after
zero extension of the query slot. The recurrence acts on selected letters
only, while all lifts use the same full joint Haar projection. -/
namespace Hindman168
open Module
open scoped Topology Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

theorem selected_alignment_slot_extension_add {n M : ℕ} (f : Fin n ↪o Fin M) {i : Fin n}
    (a b : AlignmentAddingPair n i → ℤ) :
    selectedAlignmentSlotExtension f (a+b) =
      selectedAlignmentSlotExtension f a + selectedAlignmentSlotExtension f b := by
  funext p
  by_cases hp : p ∈ Set.range (fun q : AlignmentAddingPair n i => q.map f)
  · obtain ⟨q,rfl⟩ := hp
    simp only [selected_alignment_slot_extension_apply, Pi.add_apply]
  · simp only [selected_alignment_slot_extension_outside f _ p hp, Pi.add_apply, add_zero]

theorem selected_alignment_slot_extension_unit {n M : ℕ} (f : Fin n ↪o Fin M) {i : Fin n}
    (p : AlignmentAddingPair n i) (z : ℤ) :
    selectedAlignmentSlotExtension f (alignmentAuxiliaryUnit p z) = Pi.single (p.map f) z := by
  funext q
  by_cases hq : q ∈ Set.range (fun a : AlignmentAddingPair n i => a.map f)
  · obtain ⟨a,rfl⟩ := hq
    rw [selected_alignment_slot_extension_apply]
    simp only [alignmentAuxiliaryUnit, Pi.single_apply,
      (selected_alignment_pair_map_injective f).eq_iff]
  · have hqp : q ≠ p.map f := fun h => hq (h ▸ Set.mem_range_self p)
    simp only [selected_alignment_slot_extension_outside f _ q hq, Pi.single_apply, if_neg hqp]

variable {ι κ : Type} [Fintype ι] {n M : ℕ} (f : Fin n ↪o Fin M) (i : Fin n) {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
  (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (f i) → ℤ)
  (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
    (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))

noncomputable def selectedAlignmentJointRouteNativeReading
    (factor : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (stored query : AlignmentAddingPair n i → ℤ)
    (y : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).Γ) : ℝ :=
  match factor B a c stored with
  | none => 0
  | some ν => obs ν (alignmentJointNativeCosetEvaluation D r v hv ν (selectedAlignmentSlotExtension f query) y)

theorem selected_alignment_joint_route_native_reading_continuous
    (factor : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ) (hobs : ∀ ν, Continuous (obs ν))
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (stored query : AlignmentAddingPair n i → ℤ) :
    Continuous (selectedAlignmentJointRouteNativeReading f i D r v hv factor obs B a c stored query) := by
  unfold selectedAlignmentJointRouteNativeReading
  cases factor B a c stored with
  | none => exact continuous_const
  | some ν => exact (hobs ν).comp (alignment_joint_native_coset_evaluation_continuous D r v hv ν _)

/-- Actual small-letter symmetries construct, rather than assume, every
one-letter identity needed by the selected ordered-word recurrence. -/
theorem selected_alignment_joint_native_letters_reading_equivariance
    (targets : ι → Finset (Fin M)) (gap : ℕ)
    (hsmall : ∀ e : AlignmentAddingPair n i, (e.map f).sourcePivot.val < gap)
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))).G)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hb : ∀ j, 1 ≤ w j ∧ w j ≤ s ∧
      b j ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H ρ hρ (w j) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))) H ρ hρ (w j+1) ≤
          (b.coord j).ker)
    (hsym : SelectedAlignmentCatalogueCosetSymmetry D r v hv targets gap H ρ hρ h)
    (factor : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
    let K := nativeRationalLayerOrbitData J H 1 ρ hρ
    let projection := fun x => nativeRationalLayerOrbitMap J H 1 ρ hρ h (weightedShearNativeProjection K b x)
    ∃ L : AlignmentAddingPair n i → weightedShearGroup (R := ℝ) w,
      ∀ e B a c stored query ν, factor B a c stored = some ν → targets ν = e.targetTail.image f →
      ∀ x : Fin m → ℝ,
        selectedAlignmentJointRouteNativeReading f i D r v hv factor obs B a c stored query
          (projection (L e • x)) =
        selectedAlignmentJointRouteNativeReading f i D r v hv factor obs B a c stored
          (query + alignmentAuxiliaryUnit e 1) (projection x) := by
  dsimp only
  obtain ⟨L,hL⟩ := selected_alignment_catalogue_common_letters_in_coordinates D r v hv targets
    (fun e : AlignmentAddingPair n i => e.map f) gap hsmall H ρ hρ h m b w hb hsym
  refine ⟨L,?_⟩
  intro e B a c stored query ν hfactor htarget x
  let index := alignmentOwnTargetIndex targets (e.map f)
  let k : AlignmentOwnTargetFactors targets (e.map f) := ⟨ν,htarget⟩
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν))
  let K := nativeRationalLayerOrbitData J H 1 ρ hρ
  let projection := fun x => nativeRationalLayerOrbitMap J H 1 ρ hρ h (weightedShearNativeProjection K b x)
  have hlift : nativeFinitePiCosetRestriction
      (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)) index (projection (L e • x)) =
    alignmentJointNativeCosetSlotTranslation (D ∘ index) (r ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) (fun _ => Pi.single (e.map f) 1)
      (nativeFinitePiCosetRestriction
        (fun ν => alignmentNativeArrayData (D ν) (r ν) (v ν) (hv ν)) index (projection x)) := by
    rw [alignment_joint_route_projection_restriction, alignment_joint_route_projection_restriction]
    exact hL e x
  simp only [selectedAlignmentJointRouteNativeReading, hfactor,
    selected_alignment_slot_extension_add, selected_alignment_slot_extension_unit]
  apply congrArg (obs ν)
  change alignmentJointNativeCosetEvaluation D r v hv (index k) _ (projection (L e • x)) = _
  rw [← alignment_joint_native_evaluation_restriction D r v hv index k _ _, hlift,
    alignment_joint_native_coset_slot_translation_evaluation,
    alignment_joint_native_evaluation_restriction]
  rfl

end Hindman168
