import Hindman168.AlignmentOriginalProductAllFacesPosterior

namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

noncomputable def selectedAlignmentOriginalProductAllFacesFailure
    {α : Type} [Fintype α] {β : Type*} [Fintype β] {M : ℕ} {pivot : Fin M} {step : ℕ}
    (models : α → NativeNilmanifoldData.{u} step) (F : MasterParameterFamily) (gap : Fin M) (q₀ w : ℕ)
    (T : Finset (Fin M)) (d : ℕ) (shift slots : α → AlignmentAddingPair M pivot → ℤ)
    (g a : ∀ ν, (models ν).G) (B : α → ℝ) (L : α → NNReal) (c C ε : ℝ)
    (y : Fin M → ℕ) : Prop :=
  ∃ weight : α → β → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) ∧
    ∃ (e : AlignmentAddingPair M pivot), e.targetTail=T ∧ e.sourcePivot < gap ∧ ∃ j : β,
      alignmentOriginalProductFaceFailure models F q₀ w T d shift slots weight g a B L c C ε e j y

end Hindman168
