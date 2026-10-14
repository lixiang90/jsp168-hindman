import Hindman168.PositivePrincipalSumRatios
import Hindman168.AlignmentIntegerNumerators

/-! Exact transport from the selected principal coordinates to the original
native alignment coordinates. The native ambient dimension is M, not n. -/
namespace Hindman168
open scoped BigOperators Classical

def principalAlignmentEmbedding {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) : Fin n ↪o Fin M :=
  OrderEmbedding.ofStrictMono (selectedPrincipalIndex e heM)
    (fun _ _ h => (energyPrincipal_strictMono e) h)

def AlignmentAddingPair.map {n M : ℕ} {i : Fin n}
    (p : AlignmentAddingPair n i) (f : Fin n ↪o Fin M) : AlignmentAddingPair M (f i) where
  sourceTail := p.sourceTail.image f
  targetTail := p.targetTail.image f
  sourcePivot := f p.sourcePivot
  source_nonempty := p.source_nonempty.image f
  target_nonempty := p.target_nonempty.image f
  source_before_target := by
    intro a ha b hb
    obtain ⟨a, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b, hb₀, rfl⟩ := Finset.mem_image.mp hb
    exact f.strictMono (p.source_before_target a ha₀ b hb₀)
  target_before_sourcePivot := by
    intro a ha
    obtain ⟨a, ha₀, rfl⟩ := Finset.mem_image.mp ha
    exact f.strictMono (p.target_before_sourcePivot a ha₀)
  sourcePivot_before := f.strictMono p.sourcePivot_before

@[simp] theorem AlignmentAddingPair.map_sourceBlock {n M : ℕ} {i : Fin n}
    (p : AlignmentAddingPair n i) (f : Fin n ↪o Fin M) :
    alignmentPairSourceBlock (p.map f) = (alignmentPairSourceBlock p).image f := by
  simp only [alignmentPairSourceBlock, AlignmentAddingPair.map, Finset.image_insert]

@[simp] theorem AlignmentAddingPair.map_targetBlock {n M : ℕ} {i : Fin n}
    (p : AlignmentAddingPair n i) (f : Fin n ↪o Fin M) :
    alignmentPairTargetBlock (p.map f) = (alignmentPairTargetBlock p).image f := by
  simp only [alignmentPairTargetBlock, AlignmentAddingPair.map, Finset.image_insert]

theorem principal_alignment_native_scale {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (w : ℕ) (T : Finset (Fin n)) :
    alignmentIntegerScale w (T.image (principalAlignmentEmbedding e heM)) =
      selectedSubsetScale M e w T := by
  rw [selectedSubsetScale_eq_master e heM]
  simp only [alignmentIntegerScale, alignmentNaturalBlock, Finset.image_image]
  rfl

theorem alignment_natural_block_product_image {n M : ℕ} (f : Fin n ↪o Fin M)
    (T : Finset (Fin n)) (x : Fin M → ℕ) :
    alignmentNaturalBlockProduct x (T.image f) =
      principalSubsetProduct T (fun k => x (f k)) := by
  exact Finset.prod_image f.injective.injOn

/-- The original native numerator at the lifted pair uses precisely the
selected scale ratio and the selected sample product. -/
theorem principal_alignment_native_numerator {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    {i : Fin n} (p : AlignmentAddingPair n i) (x : Fin M → ℕ) :
    (alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x : ℚ) =
      (selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) /
        ((q₀ : ℚ) * selectedSubsetScale M e w (alignmentPairTargetBlock p)) *
      principalSubsetProduct (alignmentPairSourceBlock p)
        (fun k => x (selectedPrincipalIndex e heM k)) := by
  rw [alignmentIntegerNumerator_rational_value hq hw,
    AlignmentAddingPair.map_sourceBlock, AlignmentAddingPair.map_targetBlock,
    principal_alignment_native_scale, principal_alignment_native_scale,
    alignment_natural_block_product_image]
  rfl

/-- After denominator clearing, one original native letter contributes
exactly the integer shift used by the principal adding-pair event. -/
theorem principal_alignment_native_letter_shift {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    {i : Fin n} (p : AlignmentAddingPair n i) (x : Fin M → ℕ)
    (b : Fin n → ℚ) (hb : ∀ k, 0 < b k) (z : ℤ)
    (hz : (z : ℚ) = (q₀ : ℚ) *
      (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)))
    (hratio : ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
      (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w /
      principalBlockCoefficient M e p.targetTail i
      (finiteScaleBlockProduct b (alignmentPairTargetBlock p)) w : ℕ) : ℚ) =
      ((selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairSourceBlock p)) /
      ((selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairTargetBlock p))) :
    z * (alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x : ℤ) =
      ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
        (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w /
        principalBlockCoefficient M e p.targetTail i
        (finiteScaleBlockProduct b (alignmentPairTargetBlock p)) w : ℕ) : ℤ) *
      principalSubsetProduct (alignmentPairSourceBlock p)
        (fun k => x (selectedPrincipalIndex e heM k)) := by
  apply Int.cast_injective (α := ℚ)
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [principal_alignment_native_numerator e heM hq hw, hz, hratio]
  have hqQ : (q₀ : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hbT := (finiteScaleBlockProduct_positive b hb (alignmentPairTargetBlock p)).ne'
  have hsT : (selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) ≠ 0 := by
    rw [← principal_alignment_native_scale e heM]
    exact_mod_cast (alignmentIntegerScale_positive w _).ne'
  field_simp

/-- The arithmetic clearing constant depends only on the finite scale list,
not on master parameters, models, or thresholds. -/
theorem principal_native_denominator_exists {n : ℕ} (B : Finset (Fin n → ℚ)) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ b ∈ B, ∀ i, ∀ p : AlignmentAddingPair n i,
      (q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range := by
  letI : ∀ i : Fin n, Fintype (AlignmentAddingPair n i) := alignmentAddingPairFintype n
  obtain ⟨q₀, hq, h⟩ := rational_finite_family_integer_multiplier
    (B.product (Finset.univ : Finset (Σ i : Fin n, AlignmentAddingPair n i)))
    (fun p => finiteScaleBlockProduct p.1 (alignmentPairSourceBlock p.2.2) /
      finiteScaleBlockProduct p.1 (alignmentPairTargetBlock p.2.2))
  refine ⟨q₀, hq, ?_⟩
  intro b hb i p
  exact h (b, ⟨i,p⟩) (Finset.mem_product.mpr ⟨hb, Finset.mem_univ _⟩)

end Hindman168
