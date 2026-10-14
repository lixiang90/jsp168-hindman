import Hindman168.AlignmentWordInflation

/-! Exact word transport under arbitrary later coordinatewise rational
scale changes. The earlier pivot's center is held fixed. -/

namespace Hindman168
open scoped Classical

def alignmentMultiplyScales {n : ℕ} (b d : Fin n → ℚ) : Fin n → ℚ :=
  fun j => b j * d j

theorem alignmentMultiplyScales_positive {n : ℕ} (b d : Fin n → ℚ)
    (hb : ∀ j, 0 < b j) (hd : ∀ j, 0 < d j) :
    ∀ j, 0 < alignmentMultiplyScales b d j := fun j => mul_pos (hb j) (hd j)

theorem alignmentMultiplyScales_block {n : ℕ} (b d : Fin n → ℚ) (B : Finset (Fin n)) :
    finiteScaleBlockProduct (alignmentMultiplyScales b d) B =
      finiteScaleBlockProduct b B * finiteScaleBlockProduct d B :=
  Finset.prod_mul_distrib

def alignmentRescaleWord {n : ℕ} {i : Fin n} (d : Fin n → ℚ)
    (w : List (AlignmentAddingPair n i × ℚ)) : List (AlignmentAddingPair n i × ℚ) :=
  w.map (fun l => (l.1, l.2 *
    (finiteScaleBlockProduct d (alignmentPairSourceBlock l.1) /
      finiteScaleBlockProduct d (alignmentPairTargetBlock l.1))))

theorem alignmentLetterScalar_rescale {n : ℕ} {i : Fin n} (b d : Fin n → ℚ)
    (e : AlignmentAddingPair n i) (γ : ℚ) :
    alignmentLetterScalar (alignmentMultiplyScales b d) (e, γ) =
      alignmentLetterScalar b (e, γ *
        (finiteScaleBlockProduct d (alignmentPairSourceBlock e) /
          finiteScaleBlockProduct d (alignmentPairTargetBlock e))) := by
  unfold alignmentLetterScalar
  rw [alignmentMultiplyScales_block, alignmentMultiplyScales_block, mul_div_mul_comm]
  ring

theorem alignmentWordValue_rescale {n : ℕ} {i : Fin n} {G : Type*} [Group G]
    (q₀ : ℕ) (b d : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentWordValue q₀ (alignmentMultiplyScales b d) L w =
      alignmentWordValue q₀ b L (alignmentRescaleWord d w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rcases l with ⟨e, γ⟩
    simp only [alignmentWordValue, alignmentRescaleWord, List.map_cons]
    rw [alignmentLetterScalar_rescale b d e γ]
    exact congrArg (fun y => L e ^ ⌊(q₀ : ℚ) * alignmentLetterScalar b
      (e, γ * (finiteScaleBlockProduct d (alignmentPairSourceBlock e) /
        finiteScaleBlockProduct d (alignmentPairTargetBlock e)))⌋ * y) ih

theorem alignmentRescaleWord_append {n : ℕ} {i : Fin n} (d : Fin n → ℚ)
    (v w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentRescaleWord d (v ++ w) = alignmentRescaleWord d v ++ alignmentRescaleWord d w :=
  List.map_append

theorem alignmentRescaleWord_compose {n : ℕ} {i : Fin n} (d e : Fin n → ℚ)
    (w : List (AlignmentAddingPair n i × ℚ)) :
    alignmentRescaleWord d (alignmentRescaleWord e w) =
      alignmentRescaleWord (alignmentMultiplyScales d e) w := by
  unfold alignmentRescaleWord
  rw [List.map_map]
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, alignmentMultiplyScales_block]
  rw [mul_div_mul_comm]
  congr 1
  ring

theorem alignment_palette_future_transport {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b d : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (B : Finset (Fin n))
    (palette : ℚ → X → Color) (leading : Finset ℚ)
    (words : Finset (List (AlignmentAddingPair n i × ℚ))) (x : X)
    (hreq : alignmentPaletteRequirement q₀ b L B palette
      (leading.image (fun a => a * finiteScaleBlockProduct d B))
      (words.image (alignmentRescaleWord d)) x) :
    alignmentPaletteRequirement q₀ (alignmentMultiplyScales b d) L B palette leading words x := by
  intro a ha w hw
  have h := hreq _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩) _
    (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  rw [alignmentMultiplyScales_block, alignmentWordValue_rescale]
  have hindex : a * (finiteScaleBlockProduct b B * finiteScaleBlockProduct d B) =
      (a * finiteScaleBlockProduct d B) * finiteScaleBlockProduct b B := by ring
  rw [hindex]
  exact h

end Hindman168
