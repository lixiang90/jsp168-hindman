import Hindman168.AlignmentCanonicalTargets
import Hindman168.PositivePrincipalSumFutureScalePaths

namespace Hindman168
open scoped Classical

/-- Real-valued request at the original leading indices and word actions.
No equality of prelimit threshold palettes is imposed. -/
def principalThresholdRequestHolds {n : ℕ} {i : Fin n} {G X κ : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G)
    (obs : Finset (Fin n) → ℚ → X → κ → ℝ) (θ : ℝ) (x : X)
    (request : AlignmentPivotRequest n i) : Prop :=
  ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ k,
    2*θ < obs (insert i request.tail)
      (a * finiteScaleBlockProduct b (insert i request.tail)) x k →
    θ < obs (insert i request.tail)
      (a * finiteScaleBlockProduct b (insert i request.tail))
      (alignmentWordValue q₀ b L word • x) k

theorem principal_threshold_future_transport {n : ℕ} {i : Fin n} {G X κ : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b d : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G)
    (obs : Finset (Fin n) → ℚ → X → κ → ℝ) (θ : ℝ) (x : X)
    (futures : Finset (Fin n → ℚ)) (hd : d ∈ futures)
    (request : AlignmentPivotRequest n i)
    (hreq : principalThresholdRequestHolds q₀ b L obs θ x
      (alignmentFutureRequest futures request)) :
    principalThresholdRequestHolds q₀ (alignmentMultiplyScales b d) L obs θ x request := by
  intro a ha word hw k hc
  have h := hreq _ (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)
    _ (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_image.mpr ⟨word, hw, rfl⟩⟩) k
  have he : (a * finiteScaleBlockProduct d (insert i request.tail)) *
      finiteScaleBlockProduct b (insert i request.tail) =
      a * finiteScaleBlockProduct (alignmentMultiplyScales b d) (insert i request.tail) := by
    rw [alignmentMultiplyScales_block]; ring
  simp only [alignmentFutureRequest, he, ← alignmentWordValue_rescale] at h
  exact h hc

theorem principal_threshold_canonical_comparison {n : ℕ} {i : Fin n}
    {G X κ : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (obs : Finset (Fin n) → ℚ → X → κ → ℝ) (θ : ℝ) (y : X)
    (hreq : ∀ request ∈ alignmentCanonicalRequests n i,
      principalThresholdRequestHolds q₀ b L obs θ y request)
    (T : Finset (Fin n)) (hT : T ∈ alignmentCanonicalTargetTails n i)
    (selected : List (AlignmentAddingPair n i))
    (hselected : selected.Sublist (alignmentCanonicalTargetPairs n i T)) (k : κ) :
    2*θ < obs (insert i T) (finiteScaleBlockProduct b (insert i T)) y k →
    θ < obs (insert i T) (finiteScaleBlockProduct b (insert i T))
      (alignmentWordValue q₀ b L (selected.map (fun e => (e, (1 : ℚ)))) • y) k := by
  have h := hreq _ (alignmentCanonicalRequests_contains ⟨T, hT⟩)
  simpa only [alignmentCanonicalRequest, alignmentTerminalRequest, one_mul] using
    h 1 (Finset.mem_singleton_self 1) _ (alignmentTerminalWords_contains _ selected hselected) k
end Hindman168
