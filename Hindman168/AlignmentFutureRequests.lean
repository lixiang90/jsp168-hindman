import Hindman168.AlignmentFutureWordTransport
import Hindman168.AlignmentUniformPivotPlan

/-! Terminal budgets include every prescribed possible later multiplier.
Their full finite product can strengthen comparisons, but never drops one. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentFutureRequest {n : ℕ} {i : Fin n}
    (futures : Finset (Fin n → ℚ)) (request : AlignmentPivotRequest n i) :
    AlignmentPivotRequest n i where
  tail := request.tail
  before := request.before
  leading := futures.biUnion (fun d => request.leading.image
    (fun a => a * finiteScaleBlockProduct d (insert i request.tail)))
  words := futures.biUnion (fun d => request.words.image (alignmentRescaleWord d))

theorem alignmentFutureRequest_leading_positive {n : ℕ} {i : Fin n}
    (futures : Finset (Fin n → ℚ)) (request : AlignmentPivotRequest n i)
    (hfutures : ∀ d ∈ futures, ∀ j, 0 < d j)
    (hleading : ∀ a ∈ request.leading, 0 < a) :
    ∀ a ∈ (alignmentFutureRequest futures request).leading, 0 < a := by
  intro a ha
  obtain ⟨d, hd, himage⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp himage
  exact mul_pos (hleading c hc)
    (finiteScaleBlockProduct_positive d (hfutures d hd) (insert i request.tail))

theorem alignmentFutureRequest_transport {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b d : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (palette : Finset (Fin n) → ℚ → X → Color)
    (x : X) (futures : Finset (Fin n → ℚ)) (hd : d ∈ futures)
    (request : AlignmentPivotRequest n i)
    (hreq : alignmentPivotRequestHolds q₀ b L palette x (alignmentFutureRequest futures request)) :
    alignmentPivotRequestHolds q₀ (alignmentMultiplyScales b d) L palette x request := by
  apply alignment_palette_future_transport q₀ b d L (insert i request.tail)
    (palette (insert i request.tail)) request.leading request.words x
  apply alignmentPaletteRequirement_mono q₀ b L (insert i request.tail)
    (palette (insert i request.tail)) x _ _ _ _ ?_ ?_ hreq
  · intro a ha
    exact Finset.mem_biUnion.mpr ⟨d, hd, ha⟩
  · intro w hw
    exact Finset.mem_biUnion.mpr ⟨d, hd, hw⟩

theorem alignmentRescaleWord_own_target {n : ℕ} {i : Fin n}
    (d : Fin n → ℚ) (T : Finset (Fin n)) (w : List (AlignmentAddingPair n i × ℚ))
    (hown : ∀ l ∈ w, alignmentPairTargetBlock l.1 = insert i T) :
    alignmentRescaleWord d w = w.map (fun l => (l.1, l.2 *
      (finiteScaleBlockProduct d (alignmentPairSourceBlock l.1) /
        finiteScaleBlockProduct d (insert i T)))) := by
  apply List.map_congr_left
  intro l hl
  rw [hown l hl]

end Hindman168
