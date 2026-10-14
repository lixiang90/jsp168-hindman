import Hindman168.SelectedAlignmentSourceFullRawReadings

/-! Frozen recipe parameters are chosen as genuine functions of the exposed
key before source selection. On supported stable fibers their values agree
with every actual anchor, independently of the chosen representative. -/
namespace Hindman168
open FiniteMass
open scoped Classical

abbrev SelectedAlignmentShortKey (M : ℕ) :=
  (Fin M → ℕ) × (Fin M → ℕ) × (Fin M → ℕ) × ℕ × ℕ

noncomputable def selectedAlignmentSourceKey {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (w : ℕ)
    (T : Finset (Fin n)) : (Fin M → ℕ) → SelectedAlignmentShortKey M :=
  alignmentShortExposureKey (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i))
    w (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM))

theorem selected_alignment_full_raw_support_cutoff {M : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (x : Fin M → ℕ) (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (j : Fin M) : x j ≤ F.cutoff w j.val ^ 2 := by
  have hne := Finsupp.mem_support_iff.mp hx
  rw [globalRawMass, piMass_apply] at hne
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ j))
  exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (rawMass_support_window _ _ hs)).1).2.le

/-- Two stable anchors of one genuine key have the same stored factor label.
The common witness is the actual raw support point y, with query zero. -/
theorem selected_alignment_full_frozen_label_eq_of_key {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ)) (hzero : 0 ∈ U)
    (x y : Fin M → ℕ)
    (hx : selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x)
    (hy : selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U y)
    (hys : y ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hkey : selectedAlignmentSourceKey F e heM i w T x = selectedAlignmentSourceKey F e heM i w T y)
    (stored : AlignmentAddingPair n i → ℤ) (hstored : stored ∈ V) :
    selectedAlignmentFullFrozenLabel F e heM i q₀ w T x stored =
      selectedAlignmentFullFrozenLabel F e heM i q₀ w T y stored := by
  have hc := alignmentGlobalRawMass_support_coprime F w y hys
  have hcut : ∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2 :=
    fun k _ => selected_alignment_full_raw_support_cutoff F w y hys (principalAlignmentEmbedding e heM k)
  have hd : |(y (principalAlignmentEmbedding e heM i):ℤ)-y (principalAlignmentEmbedding e heM i)| ≤
      (C*selectedPrincipalMicrocellWidth F e w i:ℕ) := by simp only [sub_self, abs_zero]; positivity
  exact (hx y hc hcut hkey stored hstored 0 hzero _ (Int.ModEq.refl _) hd).symm.trans
    (hy y hc hcut rfl stored hstored 0 hzero _ (Int.ModEq.refl _) hd)

noncomputable def selectedAlignmentKeyRepresentative {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ))
    (key : SelectedAlignmentShortKey M) : Fin M → ℕ :=
  if h : ∃ x, x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support ∧
      selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x ∧
      selectedAlignmentSourceKey F e heM i w T x = key then Classical.choose h else fun _ => 1

theorem selected_alignment_key_representative_spec {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ))
    (key : SelectedAlignmentShortKey M)
    (hex : ∃ x, x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support ∧
      selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x ∧
      selectedAlignmentSourceKey F e heM i w T x = key) :
    let x := selectedAlignmentKeyRepresentative F e heM i q₀ w C T V U key
    x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support ∧
      selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x ∧
      selectedAlignmentSourceKey F e heM i w T x = key := by
  dsimp only [selectedAlignmentKeyRepresentative]
  rw [dif_pos hex]
  exact Classical.choose_spec hex

noncomputable def selectedAlignmentKeyLabel {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ))
    (key : SelectedAlignmentShortKey M) (stored : AlignmentAddingPair n i → ℤ) : ℤ × ℤ :=
  selectedAlignmentFullFrozenLabel F e heM i q₀ w T
    (selectedAlignmentKeyRepresentative F e heM i q₀ w C T V U key) stored

theorem selected_alignment_key_label_eq {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ)) (hzero : 0 ∈ U)
    (x : Fin M → ℕ) (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hx : selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x)
    (stored : AlignmentAddingPair n i → ℤ) (hstored : stored ∈ V) :
    selectedAlignmentKeyLabel F e heM i q₀ w C T V U
      (selectedAlignmentSourceKey F e heM i w T x) stored =
      selectedAlignmentFullFrozenLabel F e heM i q₀ w T x stored := by
  have hr := selected_alignment_key_representative_spec F e heM i q₀ w C T V U
    (selectedAlignmentSourceKey F e heM i w T x) ⟨x,hxs,hx,rfl⟩
  exact selected_alignment_full_frozen_label_eq_of_key F e heM i q₀ w C T V U hzero _ x
    hr.2.1 hx hxs hr.2.2 stored hstored

/-- This single construction handles observer, translation and basepoint
recipes, all fixed as functions of w and the exposed key. -/
noncomputable def selectedAlignmentKeyRecipe {α : Type*} {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ))
    (stored : AlignmentAddingPair n i → ℤ) (recipe : ℕ → (ℤ × ℤ) → α) :
    ℕ → SelectedAlignmentShortKey M → α :=
  fun w key => recipe w (selectedAlignmentKeyLabel F e heM i q₀ w C T V U key stored)

theorem selected_alignment_key_recipe_eq {α : Type*} {n M : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n) (q₀ w C : ℕ)
    (T : Finset (Fin n)) (V U : Finset (AlignmentAddingPair n i → ℤ)) (hzero : 0 ∈ U)
    (x : Fin M → ℕ) (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hx : selectedAlignmentFullExposureArrayStable F e heM i q₀ w C T V U x)
    (stored : AlignmentAddingPair n i → ℤ) (hstored : stored ∈ V)
    (recipe : ℕ → (ℤ × ℤ) → α) :
    selectedAlignmentKeyRecipe F e heM i q₀ C T V U stored recipe w
      (selectedAlignmentSourceKey F e heM i w T x) =
      recipe w (selectedAlignmentFullFrozenLabel F e heM i q₀ w T x stored) := by
  unfold selectedAlignmentKeyRecipe
  rw [selected_alignment_key_label_eq F e heM i q₀ w C T V U hzero x hxs hx stored hstored]

end Hindman168
