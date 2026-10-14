import Hindman168.AlignmentOriginalContinuousCubeMean
import Hindman168.FinitePiProductLinearMeans

/-! The COMPLETE continuous original cube test's product-span approximants
have the EXACT finite linear combination of registered ORIGINAL product means.
All coefficients, original slots, weights, endpoints and source data remain. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical
universe u
variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (q₀ w : ℕ)
  (T : Finset (Fin N)) (y : Fin N → ℕ) (p : ℤ) (d : ℕ)
  (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
  (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
  (g a : ∀ ν, (D ν).G)

theorem alignment_original_continuous_cube_product_linear_mean :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ l : List (ℂ × (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ))),
      alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a
        (finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l)=
      (l.map (fun t => t.1*alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper
        shift slots weight g a (fun ν => t.2 ν))).sum := by
  intro l
  unfold alignmentOriginalContinuousCubeMean
  rw [complex_expectation_finite_pi_product_linear_combination]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _ht
  have hh := alignment_original_continuous_cube_product_mean D F q₀ w T y p d ellResidue lower upper
    shift slots weight g a t.2
  exact congrArg (fun z : ℂ => t.1*z) hh

end Hindman168
