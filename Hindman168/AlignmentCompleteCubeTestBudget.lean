import Hindman168.AlignmentOriginalCubeTestApproximation
import Hindman168.FiniteProductApproximationBudgets

/-! Actual common original coordinate observer bounds and retained coefficient
budget for the COMPLETE numerical cube test class. All choices precede tests,
source formulae, original endpoints/residues and actual posterior samples. -/
namespace Hindman168
open scoped BigOperators Classical NNReal
universe u
variable {ι : Type} [Fintype ι] {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)

theorem alignment_complete_cube_test_common_product_budget (B : ℝ) (L : NNReal) :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ ε : ℝ, 0 < ε → ∃ (B' : ι → ℝ) (L' : ι → NNReal) (R : ℝ),
      (∀ ν, 0 < B' ν) ∧ 0 < R ∧
      ∀ F ∈ boundedComplexLipschitzObservables (∀ ν, (D ν).G ⧸ (D ν).Γ) B L,
        ∃ l : List (ℂ × (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ))),
          (∀ t ∈ l, ∀ ν, t.2 ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B' ν) (L' ν)) ∧
          (l.map (fun t => ‖t.1‖)).sum < R ∧
          ‖F-finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l‖ < ε := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro ε hε
  obtain ⟨P,hP,hclose⟩ := alignment_original_complete_cube_test_product_approximation D B L ε hε
  obtain ⟨terms,B',L',R,hB',hR,hterms⟩ := finite_product_span_common_budgets
    (fun ν => (D ν).G ⧸ (D ν).Γ) P hP
  refine ⟨B',L',R,hB',hR,?_⟩
  intro F hF
  obtain ⟨G,hG,hcloseG⟩ := hclose F hF
  refine ⟨terms G,(hterms G hG).2.1,(hterms G hG).2.2,?_⟩
  rw [←(hterms G hG).1]
  exact hcloseG

end Hindman168
