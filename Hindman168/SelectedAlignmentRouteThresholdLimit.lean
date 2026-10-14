import Hindman168.AlignmentJointRouteReadingsCover

/-! The actual finite route comparison indices instantiate the closed/open
Portmanteau threshold theorem. The resulting prelimit event is the original
real implication 2 theta < center -> theta < terminal, never palette equality. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology Classical ENNReal

abbrev SelectedAlignmentRouteComparisonIndex {n : ℕ} {i : Fin n}
    (requests : List (AlignmentPivotRequest n i)) (κ : Type*) :=
  Σ j : Fin requests.length,
    {a // a ∈ (requests.get j).leading} × {word // word ∈ (requests.get j).words} × κ

instance selectedAlignmentRouteComparisonIndex_finite {n : ℕ} {i : Fin n}
    (requests : List (AlignmentPivotRequest n i)) (κ : Type*) [Finite κ] :
    Finite (SelectedAlignmentRouteComparisonIndex requests κ) := inferInstance

theorem selected_alignment_route_comparison_forall {n : ℕ} {i : Fin n} {κ : Type*}
    (requests : List (AlignmentPivotRequest n i))
    (P : AlignmentPivotRequest n i → ℚ → List (AlignmentAddingPair n i × ℚ) → κ → Prop) :
    (∀ j : SelectedAlignmentRouteComparisonIndex requests κ,
      P (requests.get j.1) j.2.1.val j.2.2.1.val j.2.2.2) ↔
    ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c, P request a word c := by
  simpa only [SelectedAlignmentRouteComparisonIndex, Sigma.forall, Prod.forall, Subtype.forall] using
    (List.forall_mem_iff_get (l := requests)
      (p := fun request => ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c, P request a word c)).symm

noncomputable def selectedAlignmentRouteCenter {n : ℕ} {i : Fin n} {X κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (j : SelectedAlignmentRouteComparisonIndex requests κ) : X → ℝ :=
  let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
  let B := insert i (requests.get j.1).tail
  read B (j.2.1.val * finiteScaleBlockProduct arithmetic.1 B) j.2.2.2 arithmetic.2.toAdd 0

noncomputable def selectedAlignmentRouteTerminal {n : ℕ} {i : Fin n} {X κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (j : SelectedAlignmentRouteComparisonIndex requests κ) : X → ℝ :=
  let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
  let B := insert i (requests.get j.1).tail
  let word := j.2.2.1.val
  let m := alignmentAuxiliaryWord q₀ arithmetic.1 word
  read B (j.2.1.val * finiteScaleBlockProduct arithmetic.1 B) j.2.2.2 (arithmetic.2.toAdd+m) m

theorem selected_alignment_route_closed_comparisons {n : ℕ} {i : Fin n} {X κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) :
    {x | ∀ j : SelectedAlignmentRouteComparisonIndex requests κ,
      selectedAlignmentRouteCenter read q₀ plan b requests route j x ≤ 3*θ/2 ∨
      3*θ/2 ≤ selectedAlignmentRouteTerminal read q₀ plan b requests route j x} =
      alignmentJointRouteClosedSet read θ q₀ plan b requests route := by
  ext x
  let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
  exact selected_alignment_route_comparison_forall requests
    (fun request a word c =>
      read (insert i request.tail) (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail))
        c arithmetic.2.toAdd 0 x ≤ 3*θ/2 ∨
      3*θ/2 ≤ read (insert i request.tail) (a * finiteScaleBlockProduct arithmetic.1 (insert i request.tail))
        c (arithmetic.2.toAdd+alignmentAuxiliaryWord q₀ arithmetic.1 word)
        (alignmentAuxiliaryWord q₀ arithmetic.1 word) x)

def selectedAlignmentRouteActualSet {n : ℕ} {i : Fin n} {X κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) : Set X :=
  {x | ∃ route ∈ routes,
    let arithmetic := alignmentJointRouteArithmetic q₀ plan b route
    ∀ request ∈ requests, ∀ a ∈ request.leading, ∀ word ∈ request.words, ∀ c,
      2*θ < read (insert i request.tail) (a*finiteScaleBlockProduct arithmetic.1 (insert i request.tail))
        c arithmetic.2.toAdd 0 x →
      θ < read (insert i request.tail) (a*finiteScaleBlockProduct arithmetic.1 (insert i request.tail))
        c (arithmetic.2.toAdd+alignmentAuxiliaryWord q₀ arithmetic.1 word)
        (alignmentAuxiliaryWord q₀ arithmetic.1 word) x}

theorem selected_alignment_route_actual_comparisons {n : ℕ} {i : Fin n} {X κ : Type*}
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (θ : ℝ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ)))) :
    principalActualComparisons θ
      (fun route : routes => selectedAlignmentRouteCenter read q₀ plan b requests route.val)
      (fun route : routes => selectedAlignmentRouteTerminal read q₀ plan b requests route.val) =
    selectedAlignmentRouteActualSet read θ q₀ plan b requests routes := by
  ext x
  constructor
  · rintro ⟨route,hr⟩
    exact ⟨route.val,route.property,(selected_alignment_route_comparison_forall requests _).mp hr⟩
  · rintro ⟨route,hr,h⟩
    exact ⟨⟨route,hr⟩,(selected_alignment_route_comparison_forall requests _).mpr h⟩

/-- The input errors concern only the actual finite center/terminal factor
catalogue. The empirical law can be the original integer joint orbit law. -/
theorem selected_alignment_route_closed_mass_actual_liminf
    {n : ℕ} {i : Fin n} {X κ I : Type*} [Finite κ]
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (LK : Filter I) (ν : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto ν LK (𝓝 μ))
    (read : Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (read_m : I → Finset (Fin n) → ℚ → κ → (AlignmentAddingPair n i → ℤ) →
      (AlignmentAddingPair n i → ℤ) → X → ℝ)
    (hread : ∀ B a c stored query, Continuous (read B a c stored query))
    (θ : ℝ) (hθ : 0 < θ) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (requests : List (AlignmentPivotRequest n i))
    (routes : Finset (List (ℕ × List (AlignmentAddingPair n i × ℚ))))
    (herr : ∀ᶠ m in LK, ∀ route ∈ routes, ∀ j : SelectedAlignmentRouteComparisonIndex requests κ, ∀ x,
      |selectedAlignmentRouteCenter (read_m m) q₀ plan b requests route j x -
        selectedAlignmentRouteCenter read q₀ plan b requests route j x| < θ/4 ∧
      |selectedAlignmentRouteTerminal (read_m m) q₀ plan b requests route j x -
        selectedAlignmentRouteTerminal read q₀ plan b requests route j x| < θ/4)
    (δ : ℝ≥0∞)
    (hmass : δ ≤ (μ : Measure X) (⋃ route : routes,
      alignmentJointRouteClosedSet read θ q₀ plan b requests route.val)) :
    δ ≤ LK.liminf (fun m => (ν m : Measure X)
      (selectedAlignmentRouteActualSet (read_m m) θ q₀ plan b requests routes)) := by
  have hh := principal_closed_mass_yields_actual_liminf LK ν μ hlim θ hθ
    (fun route : routes => selectedAlignmentRouteCenter read q₀ plan b requests route.val)
    (fun route : routes => selectedAlignmentRouteTerminal read q₀ plan b requests route.val)
    (fun route j => hread _ _ _ _ _) (fun route j => hread _ _ _ _ _)
    (fun m route => selectedAlignmentRouteCenter (read_m m) q₀ plan b requests route.val)
    (fun m route => selectedAlignmentRouteTerminal (read_m m) q₀ plan b requests route.val)
    (herr.mono (fun m hm => ⟨fun route j x => (hm route.val route.property j x).1,
      fun route j x => (hm route.val route.property j x).2⟩)) δ (by
      simpa only [principalClosedComparisons, selected_alignment_route_closed_comparisons] using hmass)
  simpa only [selected_alignment_route_actual_comparisons] using hh

end Hindman168
