import Hindman168.AlignmentJointRouteReadingsCover

/-! A finite catalogue of the precise stored factors appearing in all closed
route options. It is computed solely from the finite recurrence plan and
incoming scales, before the coset or the selected lifts. Terminal membership
is proved rather than assumed. -/
namespace Hindman168
open scoped Classical

abbrev AlignmentJointRouteFactor {n : ℕ} (i : Fin n) (κ : Type*) :=
  Finset (Fin n) × ℚ × κ × (AlignmentAddingPair n i → ℤ)

noncomputable def alignmentJointRouteFactorCatalogue {n : ℕ} {i : Fin n}
    (κ : Type*) [Fintype κ] (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i)) :
    Finset (AlignmentJointRouteFactor i κ) :=
  incoming.biUnion fun b => (principalPivotRoutes plan).biUnion fun route =>
    requests.toFinset.biUnion fun request => request.leading.biUnion fun a =>
      Finset.univ.biUnion fun c : κ =>
        let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
        let B := insert i request.tail
        let lead := a * finiteScaleBlockProduct arithmetic.1 B
        {(B, lead, c, arithmetic.2.toAdd)} ∪
          request.words.image (fun word => (B, lead, c,
            arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word))

theorem alignment_joint_route_center_factor_mem {n : ℕ} {i : Fin n}
    (κ : Type*) [Fintype κ] (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan)
    (request : AlignmentPivotRequest n i) (hrequest : request ∈ requests)
    (a : ℚ) (ha : a ∈ request.leading) (c : κ) :
    let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
    (insert i request.tail, a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail),
      c, arithmetic.2.toAdd) ∈ alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests := by
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨route, hr,
    Finset.mem_biUnion.mpr ⟨request, List.mem_toFinset.mpr hrequest,
      Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c,
        Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩⟩⟩⟩⟩

theorem alignment_joint_route_terminal_factor_mem {n : ℕ} {i : Fin n}
    (κ : Type*) [Fintype κ] (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (requests : List (AlignmentPivotRequest n i))
    (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan)
    (request : AlignmentPivotRequest n i) (hrequest : request ∈ requests)
    (a : ℚ) (ha : a ∈ request.leading)
    (word : List (AlignmentAddingPair n i × ℚ)) (hw : word ∈ request.words) (c : κ) :
    let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
    (insert i request.tail, a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail), c,
      arithmetic.2.toAdd + alignmentAuxiliaryWord q₀ arithmetic.1 word) ∈
        alignmentJointRouteFactorCatalogue κ q₀ plan incoming requests := by
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_biUnion.mpr ⟨route, hr,
    Finset.mem_biUnion.mpr ⟨request, List.mem_toFinset.mpr hrequest,
      Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c,
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨word, hw, rfl⟩)⟩⟩⟩⟩⟩

/-- Lookup in a genuinely finite stored-factor family. -/
noncomputable def alignmentJointFiniteFactorLookup {n : ℕ} {i : Fin n} {κ : Type*}
    (catalogue : Finset (AlignmentJointRouteFactor i κ))
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (stored : AlignmentAddingPair n i → ℤ) :
    Option catalogue :=
  if h : (B,a,c,stored) ∈ catalogue then some ⟨(B,a,c,stored), h⟩ else none

theorem alignment_joint_finite_factor_lookup_mem {n : ℕ} {i : Fin n} {κ : Type*}
    (catalogue : Finset (AlignmentJointRouteFactor i κ))
    (B : Finset (Fin n)) (a : ℚ) (c : κ) (stored : AlignmentAddingPair n i → ℤ)
    (hmem : (B,a,c,stored) ∈ catalogue) :
    alignmentJointFiniteFactorLookup catalogue B a c stored = some ⟨(B,a,c,stored), hmem⟩ := by
  simp only [alignmentJointFiniteFactorLookup, dif_pos hmem]

/-- Every terminal letter in a canonical request belongs to that request's
own target; no such assertion is made about arbitrary cumulative jumps. -/
theorem alignment_canonical_request_words_own_target {n : ℕ} {i : Fin n}
    (request : AlignmentPivotRequest n i) (hr : request ∈ alignmentCanonicalRequests n i)
    (word : List (AlignmentAddingPair n i × ℚ)) (hw : word ∈ request.words)
    (l : AlignmentAddingPair n i × ℚ) (hl : l ∈ word) :
    l.1.targetTail = request.tail := by
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hr
  change word ∈ alignmentTerminalWords (alignmentCanonicalTargetPairs n i T.val) at hw
  obtain ⟨selected, hs, rfl⟩ := Finset.mem_image.mp hw
  have hsub := List.mem_sublists.mp (List.mem_toFinset.mp hs)
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
  exact (alignmentCanonicalTargetPairs_contains T.val e).mp (hsub.subset he)

/-- Future rescaling changes coefficients but never the own-target letters. -/
theorem alignment_future_request_words_own_target {n : ℕ} {i : Fin n}
    (futures : Finset (Fin n → ℚ)) (request : AlignmentPivotRequest n i)
    (hown : ∀ word ∈ request.words, ∀ l ∈ word, l.1.targetTail = request.tail)
    (word : List (AlignmentAddingPair n i × ℚ))
    (hw : word ∈ (alignmentFutureRequest futures request).words)
    (l : AlignmentAddingPair n i × ℚ) (hl : l ∈ word) :
    l.1.targetTail = (alignmentFutureRequest futures request).tail := by
  obtain ⟨d, _, himage⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨word0, hw0, rfl⟩ := Finset.mem_image.mp himage
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  exact hown word0 hw0 a ha

/-- The stored-factor target is intrinsic to its block, independent of the
route, coset and selected lift. -/
theorem alignment_request_factor_target {n : ℕ} {i : Fin n}
    (request : AlignmentPivotRequest n i) :
    (insert i request.tail).erase i = request.tail := by
  have hi : i ∉ request.tail := fun hi => (lt_irrefl i) (request.before i hi)
  exact Finset.erase_insert hi

end Hindman168
