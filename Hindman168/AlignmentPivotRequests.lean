import Hindman168.AlignmentStageAdvance
import Hindman168.AlignmentPlanFiniteScales

/-! Actual requests and stages for a fixed pivot. A predecessor request
retains its target and replaces its budgets by the proved all-choice unions. -/

namespace Hindman168
universe u v
open scoped Classical

structure AlignmentPivotRequest (n : ℕ) (i : Fin n) where
  tail : Finset (Fin n)
  before : ∀ j ∈ tail, j < i
  leading : Finset ℚ
  words : Finset (List (AlignmentAddingPair n i × ℚ))

structure AlignmentPivotStage (n : ℕ) (i : Fin n) where
  target : AlignmentPivotRequest n i
  choices : Finset (ℕ × List (AlignmentAddingPair n i × ℚ))

def alignmentPivotRequestHolds {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G)
    (palette : Finset (Fin n) → ℚ → X → Color) (x : X)
    (request : AlignmentPivotRequest n i) : Prop :=
  alignmentPaletteRequirement q₀ b L (insert i request.tail)
    (palette (insert i request.tail)) request.leading request.words x

noncomputable def alignmentPivotPredecessor {n : ℕ} {i : Fin n}
    (stage : AlignmentPivotStage n i) (request : AlignmentPivotRequest n i) :
    AlignmentPivotRequest n i where
  tail := request.tail
  before := request.before
  leading := alignmentChoicePredecessorLeading stage.target.tail (insert i request.tail)
    stage.choices request.leading
  words := alignmentChoicePredecessorWords stage.target.tail stage.choices request.words

def AlignmentPivotStageWorks {n : ℕ} {i : Fin n} (s : ℕ) (Color : Type)
    (stage : AlignmentPivotStage n i) : Prop :=
  (∀ p ∈ stage.choices, 0 < p.1) ∧
  ∀ (G : Type u) [Group G] (X : Type v) [MulAction G X]
    (q₀ : ℕ) (b : Fin n → ℚ) (L : AlignmentAddingPair n i → G),
    (∀ l ∈ alignmentWordLetters stage.target.words,
      (q₀ : ℚ) * alignmentLetterScalar b l ∈ (Int.castRingHom ℚ).range) →
    ∀ (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
      (palette : Finset (Fin n) → ℚ → X → Color) (x : X), ∃ p ∈ stage.choices,
      alignmentPivotRequestHolds q₀ (alignmentScaleUpdate i stage.target.tail p.1 b) L
        palette (alignmentWordValue q₀ b L p.2 • x) stage.target

theorem alignment_pivot_stage_exists {n : ℕ} {i : Fin n} {Color : Type} [Finite Color]
    (s : ℕ) (hrec : HasAlignmentMonomialRecurrence s)
    (request : AlignmentPivotRequest n i) :
    ∃ choices, AlignmentPivotStageWorks.{u, v} s Color
      ({target := request, choices := choices} : AlignmentPivotStage n i) := by
  obtain ⟨Ω, hpos, hΩ⟩ := alignment_actual_target_choices.{u, v} (Color := Color)
    s hrec request.tail request.before request.leading request.words
  refine ⟨Ω, hpos, ?_⟩
  intro G _ X _ q₀ b L hint hG palette x
  exact hΩ G X q₀ b L hint hG (palette (insert i request.tail)) x

theorem alignment_pivot_predecessor_preserves {n : ℕ} {i : Fin n} {G X Color : Type*}
    [Group G] [MulAction G X] (q₀ : ℕ) (b : Fin n → ℚ)
    (L : AlignmentAddingPair n i → G) (palette : Finset (Fin n) → ℚ → X → Color)
    (x : X) (stage : AlignmentPivotStage n i) (request : AlignmentPivotRequest n i)
    (p : ℕ × List (AlignmentAddingPair n i × ℚ)) (hp : p ∈ stage.choices) (hk : 0 < p.1)
    (hreq : alignmentPivotRequestHolds q₀ b L palette x (alignmentPivotPredecessor stage request)) :
    alignmentPivotRequestHolds q₀ (alignmentScaleUpdate i stage.target.tail p.1 b) L
      palette (alignmentWordValue q₀ b L p.2 • x) request := by
  exact alignment_all_choices_predecessor_preserves q₀ b L stage.target.tail
    (insert i request.tail) stage.choices request.leading request.words
    (palette (insert i request.tail)) x hreq p hp hk

theorem alignment_pivot_predecessor_positive {n : ℕ} {i : Fin n}
    (stage : AlignmentPivotStage n i) (request : AlignmentPivotRequest n i)
    (hstage : ∀ p ∈ stage.choices, 0 < p.1)
    (hleading : ∀ a ∈ request.leading, 0 < a) :
    ∀ a ∈ (alignmentPivotPredecessor stage request).leading, 0 < a :=
  alignmentChoicePredecessorLeading_positive stage.target.tail (insert i request.tail)
    stage.choices request.leading hstage hleading

end Hindman168
