import Hindman168.SelectedAlignmentSourceExtension

/-! Exact selected numerical data use original ambient master scales. They
are literally the data of the mapped original adding pairs on the one-filled
sample extension, without changing the common modulus or scale dimension. -/
namespace Hindman168
open scoped Classical

noncomputable def selectedAlignmentIntegerNumerator {n : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (q₀ w : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) : ℕ :=
  (selectedSubsetScale M e w (alignmentPairSourceBlock p) /
    (q₀ * selectedSubsetScale M e w (alignmentPairTargetBlock p))) *
      principalSubsetProduct (alignmentPairSourceBlock p) x

noncomputable def selectedAlignmentPairResidue {n : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) : ℕ :=
  alignmentResidueRepresentative (selectedAlignmentIntegerNumerator M e q₀ w p x)
    (principalSubsetProduct p.targetTail x) (modulus * (primorial w)^w)

noncomputable def selectedAlignmentPairProgression {n : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) : ℤ :=
  alignmentProgressionShift (selectedAlignmentIntegerNumerator M e q₀ w p x)
    (principalSubsetProduct p.targetTail x) (selectedAlignmentPairResidue M e q₀ w modulus p x) modulus

@[simp] theorem selected_alignment_native_integer_numerator {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) :
    alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM))
      (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) =
      selectedAlignmentIntegerNumerator M e q₀ w p x := by
  unfold alignmentIntegerNumerator selectedAlignmentIntegerNumerator
  rw [AlignmentAddingPair.map_sourceBlock, AlignmentAddingPair.map_targetBlock,
    principal_alignment_native_scale, principal_alignment_native_scale, selected_alignment_block_product]

@[simp] theorem selected_alignment_native_pair_residue {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) :
    alignmentPairResidue q₀ w modulus (p.map (principalAlignmentEmbedding e heM))
      (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) =
      selectedAlignmentPairResidue M e q₀ w modulus p x := by
  unfold alignmentPairResidue selectedAlignmentPairResidue
  rw [selected_alignment_native_integer_numerator]
  change alignmentResidueRepresentative _
    (alignmentNaturalBlockProduct _ (p.targetTail.image (principalAlignmentEmbedding e heM))) _ = _
  rw [selected_alignment_block_product]

@[simp] theorem selected_alignment_native_pair_progression {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin n → ℕ) :
    alignmentPairProgression q₀ w modulus (p.map (principalAlignmentEmbedding e heM))
      (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) =
      selectedAlignmentPairProgression M e q₀ w modulus p x := by
  unfold alignmentPairProgression selectedAlignmentPairProgression
  rw [selected_alignment_native_integer_numerator, selected_alignment_native_pair_residue]
  change alignmentProgressionShift _
    (alignmentNaturalBlockProduct _ (p.targetTail.image (principalAlignmentEmbedding e heM))) _ _ = _
  rw [selected_alignment_block_product]

/-- Exact selected array identity for the canonical original data. -/
theorem selected_alignment_canonical_array_argument {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (x : Fin n → ℕ) (T : Finset (Fin n)) (p : ℤ)
    (stored query : AlignmentAddingPair n i → ℤ) :
    let f := principalAlignmentEmbedding e heM
    let y := selectedAlignmentSampleExtension f x
    alignmentIntegerArrayArgument y modulus (fun p => alignmentPairResidue q₀ w modulus p y)
      (fun p => alignmentPairProgression q₀ w modulus p y) (T.image f) p
      (selectedAlignmentSlotExtension f stored) (selectedAlignmentSlotExtension f query) =
    alignmentIntegerArrayArgument x modulus (fun p => selectedAlignmentPairResidue M e q₀ w modulus p x)
      (fun p => selectedAlignmentPairProgression M e q₀ w modulus p x) T p stored query := by
  dsimp only
  rw [selected_alignment_integer_array_argument]
  simp only [selected_alignment_native_pair_residue, selected_alignment_native_pair_progression]

end Hindman168
