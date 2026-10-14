import Hindman168.AlignmentFutureRequests
import Mathlib.Data.List.Sublists

/-! A fixed ordered pair list supplies every subset test through its
sublists. Future transport yields the paper coefficients d_A/d_B exactly. -/

namespace Hindman168
open scoped Classical

noncomputable def alignmentTerminalWords {n : ℕ} {i : Fin n}
    (ordered : List (AlignmentAddingPair n i)) : Finset (List (AlignmentAddingPair n i × ℚ)) :=
  ordered.sublists.toFinset.image (List.map (fun e => (e, (1 : ℚ))))

noncomputable def alignmentTerminalRequest {n : ℕ} {i : Fin n}
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (ordered : List (AlignmentAddingPair n i)) : AlignmentPivotRequest n i where
  tail := T
  before := hT
  leading := {1}
  words := alignmentTerminalWords ordered

theorem alignmentTerminalWords_contains {n : ℕ} {i : Fin n}
    (ordered selected : List (AlignmentAddingPair n i)) (hselected : selected.Sublist ordered) :
    selected.map (fun e => (e, (1 : ℚ))) ∈ alignmentTerminalWords ordered :=
  Finset.mem_image.mpr ⟨selected, List.mem_toFinset.mpr (List.mem_sublists.mpr hselected), rfl⟩

theorem alignmentTerminalWords_filter_contains {n : ℕ} {i : Fin n}
    (ordered : List (AlignmentAddingPair n i)) (D : Finset (AlignmentAddingPair n i)) :
    (ordered.filter (fun e => e ∈ D)).map (fun e => (e, (1 : ℚ))) ∈
      alignmentTerminalWords ordered :=
  alignmentTerminalWords_contains ordered _ List.filter_sublist

theorem alignmentTerminalWords_filter_support {n : ℕ} {i : Fin n}
    (ordered : List (AlignmentAddingPair n i)) (D : Finset (AlignmentAddingPair n i))
    (hD : D ⊆ ordered.toFinset) : (ordered.filter (fun e => e ∈ D)).toFinset = D := by
  ext e
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hD h), h⟩⟩

theorem alignmentTerminalWords_future_coefficients {n : ℕ} {i : Fin n}
    (d : Fin n → ℚ) (T : Finset (Fin n))
    (ordered selected : List (AlignmentAddingPair n i))
    (hown : ∀ e ∈ ordered, e.targetTail = T) (hselected : selected.Sublist ordered) :
    alignmentRescaleWord d (selected.map (fun e => (e, (1 : ℚ)))) =
      selected.map (fun e => (e, finiteScaleBlockProduct d (alignmentPairSourceBlock e) /
        finiteScaleBlockProduct d (insert i T))) := by
  unfold alignmentRescaleWord
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_apply, one_mul]
  rw [alignmentPairTargetBlock, hown e (hselected.subset he)]

theorem alignmentTerminalRequest_future_comparison {n : ℕ} {i : Fin n}
    {G X Color : Type*} [Group G] [MulAction G X]
    (q₀ : ℕ) (b d : Fin n → ℚ) (L : AlignmentAddingPair n i → G)
    (palette : Finset (Fin n) → ℚ → X → Color) (x : X)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (ordered selected : List (AlignmentAddingPair n i))
    (hselected : selected.Sublist ordered) (futures : Finset (Fin n → ℚ)) (hd : d ∈ futures)
    (hreq : alignmentPivotRequestHolds q₀ b L palette x
      (alignmentFutureRequest futures (alignmentTerminalRequest T hT ordered))) :
    palette (insert i T) (finiteScaleBlockProduct (alignmentMultiplyScales b d) (insert i T)) x =
      palette (insert i T) (finiteScaleBlockProduct (alignmentMultiplyScales b d) (insert i T))
        (alignmentWordValue q₀ (alignmentMultiplyScales b d) L
          (selected.map (fun e => (e, (1 : ℚ)))) • x) := by
  have h := alignmentFutureRequest_transport q₀ b d L palette x futures hd
    (alignmentTerminalRequest T hT ordered) hreq
  simpa only [alignmentTerminalRequest, one_mul] using h 1 (Finset.mem_singleton_self 1) _
    (alignmentTerminalWords_contains ordered selected hselected)

end Hindman168
