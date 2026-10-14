import Hindman168.PositivePrincipalSumFinalDeduction
import Hindman168.NativePieceRecipes

/-! Exact remaining uniform alignment input. All finite arithmetic
catalogues and positive probability constants precede parameters, selected
indices, models, their complexity, and the threshold. This is a definition,
not an assertion that Principle 2.4 has already been proved. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical
universe u

def HasUniformSelectedPrincipalAlignment : Prop :=
  ∀ n r s : ℕ, ∃ B : Finset (Fin n → ℚ), ∃ A : Finset ℚ,
    ∃ hclosed : FiniteScaleClosure B A,
    B.Nonempty ∧ (∀ b ∈ B, ∀ i, 0 < b i) ∧ (∀ a ∈ A, 0 < a) ∧
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (d M : ℕ) (hM : 0 < M) (P : Finset (MvPolynomial (Fin d) ℤ)) (F : MasterParameterFamily),
      MasterParameterConditions M A P F →
      ∀ (e : Fin (2*n) ↪o ℕ), (∀ j, e j < M) →
      ∀ S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ,
      (∀ T i γ, NativePieceRepresented.{u} s F
        (masterGapIndex M hM (energyPadding e i)) (S T i γ)) →
      (∀ T i γ w y, S T i γ w y ∈ Set.Icc (0 : ℝ) 1) →
      ∀ θ : ℝ, 0 < θ →
        δ ≤ Filter.liminf (fun w => event (selectedPrincipalRawMass e F w)
          (PrincipalSumAlignmentEvent M e B A hclosed S θ w)) atTop
end Hindman168
