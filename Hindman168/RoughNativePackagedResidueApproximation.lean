import Hindman168.RoughNativeFiniteResidueApproximation
import Hindman168.RoughNativeKernelNilmanifold

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_packaged_residue_approximation {s : ℕ} {ι : Type*} [Fintype ι]
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (residue : ι → ℤ) (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    let N := fun j => roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (residue j)
    let L := nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ)
    let σ := fun j => nativeLieExponential (I := D.I) (G := D.G) ((residue j : ℝ) • V)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((N j).G ⧸ (N j).Γ) := fun j => (N j).metric
    letI : ∀ j, TopologicalSpace ((N j).G ⧸ (N j).Γ) := fun j =>
      (N j).metric.toUniformSpace.toTopologicalSpace
    ∃ K : NNReal, ∀ (j : ι) (b : ℝ), |b| ≤ R → ∀ F : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) → ∃ f : (N j).G ⧸ (N j).Γ → ℝ,
        LipschitzWith K f ∧
          (∀ x, |F (roughConjugateOrbitMap D.Γ L (σ j)
            (nativeLieExponential (I := D.I) (G := D.G) (b • V)) x) - f x| ≤ ε) ∧
          (∀ x, |f x| ≤ B) := by
  exact rough_native_finite_residue_lipschitz_approximation D S hS χ hχ hQ V hVr
    residue R B hB Lip hε

end Hindman168
