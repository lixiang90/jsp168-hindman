import Hindman168.SelectedAlignmentCatalogueLettersReadings
import Hindman168.SelectedAlignmentRouteThresholdLimit
import Hindman168.PositivePrincipalSumFutureObservation

/-! Numerical meaning of the actual prelimit route readings. The raw sample
is fixed throughout. A stored slot moves the signed pivot by its residue
shift; an own word also changes the progression slot. -/
namespace Hindman168
open scoped BigOperators Classical

noncomputable def selectedAlignmentRouteRawReading {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (B : Finset (Fin n)) (a : ℚ) (c : κ)
    (stored query : AlignmentAddingPair n i → ℤ) (p : ℤ) : ℝ :=
  S (B.erase i) a c w (alignmentIntegerArrayArgument x (F.modulus w)
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
    (fun e => alignmentPairProgression q₀ w (F.modulus w) e x)
    ((B.erase i).image f) p
    (selectedAlignmentSlotExtension f stored) (selectedAlignmentSlotExtension f query))

/-- The original native observation with an independent signed pivot.
The earlier raw coordinates and every original master parameter are retained. -/
noncomputable def selectedAlignmentSignedScaleObservation {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ) (p : ℤ) :
    Finset (Fin n) → ℚ → Multiplicative (AlignmentAddingPair M (f i) → ℤ) → κ → ℝ :=
  fun B a u c => S (B.erase i) a c w (alignmentIntegerArrayArgument x (F.modulus w)
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
    (fun e => alignmentPairProgression q₀ w (F.modulus w) e x)
    ((B.erase i).image f) p u.toAdd u.toAdd)

theorem selected_alignment_slot_extension_zero {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) :
    selectedAlignmentSlotExtension f (0 : AlignmentAddingPair n i → ℤ) = 0 := by
  funext p
  by_cases hp : p ∈ Set.range (fun q : AlignmentAddingPair n i => q.map f)
  · obtain ⟨q,rfl⟩ := hp
    exact selected_alignment_slot_extension_apply f 0 q
  · exact selected_alignment_slot_extension_outside f 0 p hp

/-- Arbitrary rational letters, including negative powers and repetitions,
have exactly the extended selected-slot word. -/
theorem selected_alignment_native_word_slots {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (q₀ : ℕ) (b : Fin n → ℚ)
    (word : List (AlignmentAddingPair n i × ℚ)) :
    (alignmentWordValue q₀ b (principalNativeLetter f) word).toAdd =
      selectedAlignmentSlotExtension f (alignmentAuxiliaryWord q₀ b word) := by
  induction word with
  | nil => exact (selected_alignment_slot_extension_zero f).symm
  | cons l word ih =>
    simp only [alignmentWordValue, toAdd_mul, toAdd_zpow, principalNativeLetter,
      toAdd_ofAdd, alignmentAuxiliaryWord, selected_alignment_slot_extension_add,
      selected_alignment_slot_extension_unit, ih]
    congr 1
    funext p
    simp [alignmentAuxiliaryUnit, Pi.single_apply, Pi.smul_apply]

theorem alignment_integer_array_argument_stored_base {M : ℕ} {i : Fin M}
    (x : Fin M → ℕ) (modulus : ℕ) (ρ : AlignmentAddingPair M i → ℕ)
    (Δ : AlignmentAddingPair M i → ℤ) (T : Finset (Fin M))
    (p : ℤ) (v u : AlignmentAddingPair M i → ℤ) :
    alignmentIntegerArrayArgument x modulus ρ Δ T p (v+u) u =
      alignmentIntegerArrayArgument x modulus ρ Δ T
        (p+alignmentIntegerSlotShift ρ v) u u := by
  simp only [alignmentIntegerArrayArgument, alignmentIntegerSlotShift_add]
  ring

/-- Center `R(v,0)` is the original observation at the shifted pivot. -/
theorem selected_alignment_route_raw_center {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (v : AlignmentAddingPair n i → ℤ) (p : ℤ) :
    selectedAlignmentRouteRawReading f i F q₀ w x S B a c v 0 p =
      selectedAlignmentSignedScaleObservation f i F q₀ w x S
        (p+alignmentIntegerSlotShift
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
          (selectedAlignmentSlotExtension f v)) B a 1 c := by
  unfold selectedAlignmentRouteRawReading selectedAlignmentSignedScaleObservation
  rw [selected_alignment_slot_extension_zero]
  simp only [toAdd_one]
  exact congrArg (S (B.erase i) a c w)
    (by simpa only [add_zero] using (alignment_integer_array_argument_stored_base x
      (F.modulus w) (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e x)
      ((B.erase i).image f) p (selectedAlignmentSlotExtension f v) 0))

/-- Terminal `R(v+m,m)` uses the same shifted base point and the actual
native group word. It is not a claim about an arbitrary pivot translation. -/
theorem selected_alignment_route_raw_terminal {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (v : AlignmentAddingPair n i → ℤ)
    (b : Fin n → ℚ) (word : List (AlignmentAddingPair n i × ℚ)) (p : ℤ) :
    selectedAlignmentRouteRawReading f i F q₀ w x S B a c
      (v+alignmentAuxiliaryWord q₀ b word) (alignmentAuxiliaryWord q₀ b word) p =
      selectedAlignmentSignedScaleObservation f i F q₀ w x S
        (p+alignmentIntegerSlotShift
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
          (selectedAlignmentSlotExtension f v)) B a
        (alignmentWordValue q₀ b (principalNativeLetter f) word • 1) c := by
  simp only [selectedAlignmentRouteRawReading, selectedAlignmentSignedScaleObservation,
    smul_eq_mul, mul_one, selected_alignment_native_word_slots,
    selected_alignment_slot_extension_add]
  rw [alignment_integer_array_argument_stored_base]

/-- The actual prelimit threshold event gives secured requests at one
explicit shifted signed pivot, with the original earlier sample unchanged. -/
theorem selected_alignment_route_raw_actual_iff {n M : ℕ} {κ : Type*}
    (f : Fin n ↪o Fin M) (i : Fin n) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → ℚ → κ → ℕ → ℤ → ℝ)
    (θ : ℝ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) (p : ℤ) :
    p ∈ selectedAlignmentRouteActualSet (selectedAlignmentRouteRawReading f i F q₀ w x S)
      θ q₀ plan b requests routes ↔
    ∃ route ∈ routes,
      let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
      ∀ request ∈ requests,
        principalThresholdRequestHolds q₀ arithmetic.1 (principalNativeLetter f)
          (selectedAlignmentSignedScaleObservation f i F q₀ w x S
            (p+alignmentIntegerSlotShift
              (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
              (selectedAlignmentSlotExtension f arithmetic.2.toAdd))) θ 1 request := by
  simp only [selectedAlignmentRouteActualSet, Set.mem_setOf_eq, principalThresholdRequestHolds,
    selected_alignment_route_raw_center, selected_alignment_route_raw_terminal]

end Hindman168
