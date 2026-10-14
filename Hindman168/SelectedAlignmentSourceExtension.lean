import Hindman168.PositivePrincipalSumNativeIndices
import Hindman168.AlignmentExposedArrayOffsets

/-! Embed selected raw coordinates and slot vectors into the ORIGINAL
M-dimensional alignment problem. Unselected raw coordinates are 1 and
unselected adding-pair slots are 0. Original master scales are never changed. -/
namespace Hindman168
open scoped BigOperators Classical
attribute [local instance] alignmentAddingPairFintype

noncomputable def selectedAlignmentSampleExtension {n M : ℕ}
    (f : Fin n ↪o Fin M) (x : Fin n → ℕ) : Fin M → ℕ :=
  Function.extend f x (fun _ => 1)

@[simp] theorem selected_alignment_sample_extension_apply {n M : ℕ}
    (f : Fin n ↪o Fin M) (x : Fin n → ℕ) (j : Fin n) :
    selectedAlignmentSampleExtension f x (f j) = x j :=
  f.injective.extend_apply x (fun _ => 1) j

theorem selected_alignment_sample_extension_outside {n M : ℕ}
    (f : Fin n ↪o Fin M) (x : Fin n → ℕ) (j : Fin M) (hj : j ∉ Set.range f) :
    selectedAlignmentSampleExtension f x j = 1 :=
  Function.extend_apply' x (fun _ => 1) j hj

theorem selected_alignment_sample_extension_coprime {n M : ℕ}
    (f : Fin n ↪o Fin M) (x : Fin n → ℕ) (W : ℕ)
    (hx : ∀ j, Nat.Coprime (x j) W) :
    ∀ j, Nat.Coprime (selectedAlignmentSampleExtension f x j) W := by
  intro j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨k, rfl⟩ := hj
    simpa only [selected_alignment_sample_extension_apply] using hx k
  · rw [selected_alignment_sample_extension_outside f x j hj]
    exact Nat.coprime_one_left _

@[simp] theorem selected_alignment_block_product {n M : ℕ}
    (f : Fin n ↪o Fin M) (T : Finset (Fin n)) (x : Fin n → ℕ) :
    alignmentNaturalBlockProduct (selectedAlignmentSampleExtension f x) (T.image f) =
      principalSubsetProduct T x := by
  rw [alignment_natural_block_product_image]
  simp only [selected_alignment_sample_extension_apply]

/-- Equality/modular exposure of selected coordinates gives the true ambient
exposure because all omitted coordinates are literally constant. -/
theorem selected_alignment_raw_exposure {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (L : ℕ) (T : Finset (Fin n)) (x y : Fin n → ℕ)
    (h : alignmentRawExposure i L T x y) :
    alignmentRawExposure (f i) L (T.image f)
      (selectedAlignmentSampleExtension f x) (selectedAlignmentSampleExtension f y) := by
  constructor
  · intro j hj hjT
    by_cases hjf : j ∈ Set.range f
    · obtain ⟨k, rfl⟩ := hjf
      simp only [selected_alignment_sample_extension_apply]
      exact h.1 k (f.lt_iff_lt.mp hj) (fun hk => hjT (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    · rw [selected_alignment_sample_extension_outside f x j hjf,
        selected_alignment_sample_extension_outside f y j hjf]
  · intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    simpa only [selected_alignment_sample_extension_apply] using h.2 k hk

/-- The map on actual ordered adding pairs is injective. -/
theorem selected_alignment_pair_map_injective {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) : Function.Injective (fun p : AlignmentAddingPair n i => p.map f) := by
  intro p q hpq
  apply alignmentAddingPair_fields_injective
  apply Prod.ext
  · exact Finset.image_injective f.injective (congrArg AlignmentAddingPair.sourceTail hpq)
  · apply Prod.ext
    · exact Finset.image_injective f.injective (congrArg AlignmentAddingPair.targetTail hpq)
    · exact f.injective (congrArg AlignmentAddingPair.sourcePivot hpq)

noncomputable def selectedAlignmentSlotExtension {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ) : AlignmentAddingPair M (f i) → ℤ :=
  Function.extend (fun p : AlignmentAddingPair n i => p.map f) u (fun _ => 0)

@[simp] theorem selected_alignment_slot_extension_apply {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ) (p : AlignmentAddingPair n i) :
    selectedAlignmentSlotExtension f u (p.map f) = u p :=
  (selected_alignment_pair_map_injective f).extend_apply u (fun _ => 0) p

theorem selected_alignment_slot_extension_outside {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ) (p : AlignmentAddingPair M (f i))
    (hp : p ∉ Set.range (fun q : AlignmentAddingPair n i => q.map f)) :
    selectedAlignmentSlotExtension f u p = 0 := Function.extend_apply' u (fun _ => 0) p hp

/-- Finite sums involving selected slots see exactly the selected letters. -/
theorem selected_alignment_slot_sum {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ)
    (g : AlignmentAddingPair M (f i) → ℤ) :
    ∑ p, selectedAlignmentSlotExtension f u p * g p = ∑ p, u p * g (p.map f) := by
  let image : Finset (AlignmentAddingPair M (f i)) := Finset.univ.image (fun p : AlignmentAddingPair n i => p.map f)
  have hs : ∑ p ∈ image, selectedAlignmentSlotExtension f u p * g p =
      ∑ p, selectedAlignmentSlotExtension f u p * g p := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [selected_alignment_slot_extension_outside f u p, zero_mul]
    intro h
    obtain ⟨q, rfl⟩ := h
    exact hp (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)
  rw [← hs]
  dsimp only [image]
  rw [Finset.sum_image (selected_alignment_pair_map_injective f).injOn]
  simp only [selected_alignment_slot_extension_apply]

theorem selected_alignment_slot_shift {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ)
    (ρ : AlignmentAddingPair M (f i) → ℕ) :
    alignmentIntegerSlotShift ρ (selectedAlignmentSlotExtension f u) =
      alignmentIntegerSlotShift (fun p => ρ (p.map f)) u :=
  selected_alignment_slot_sum f u (fun p => (ρ p : ℤ))

theorem selected_alignment_array_progression {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (u : AlignmentAddingPair n i → ℤ)
    (Δ : AlignmentAddingPair M (f i) → ℤ) (T : Finset (Fin n)) :
    alignmentIntegerArrayProgression Δ (T.image f) (selectedAlignmentSlotExtension f u) =
      alignmentIntegerArrayProgression (fun p => Δ (p.map f)) T u := by
  simpa only [alignmentIntegerArrayProgression, mul_ite, mul_zero,
    AlignmentAddingPair.map, Finset.image_inj f.injective] using
    selected_alignment_slot_sum f u (fun p => if p.targetTail = T.image f then Δ p else 0)

/-- Exact original M-dimensional integer array argument, including all
residue and progression shifts. This is not a compressed master scale. -/
theorem selected_alignment_integer_array_argument {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (x : Fin n → ℕ) (modulus : ℕ)
    (ρ : AlignmentAddingPair M (f i) → ℕ) (Δ : AlignmentAddingPair M (f i) → ℤ)
    (T : Finset (Fin n)) (p : ℤ) (stored query : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument (selectedAlignmentSampleExtension f x) modulus ρ Δ (T.image f) p
      (selectedAlignmentSlotExtension f stored) (selectedAlignmentSlotExtension f query) =
      alignmentIntegerArrayArgument x modulus (fun e => ρ (e.map f)) (fun e => Δ (e.map f)) T p stored query := by
  unfold alignmentIntegerArrayArgument
  rw [selected_alignment_block_product, selected_alignment_slot_shift, selected_alignment_array_progression]
  rfl

end Hindman168
