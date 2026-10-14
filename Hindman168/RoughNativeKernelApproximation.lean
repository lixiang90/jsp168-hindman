import Hindman168.RoughNativeOrbitApproximation
import Hindman168.RoughNativeKernelOrbit

namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_residue_kernel_lipschitz_approximation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    let L := nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ)
    let σ := nativeLieExponential (I := D.I) (G := D.G) ((j : ℝ) • V)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := roughNativeOrbitSourceMetric D L σ
    letI : TopologicalSpace (L ⧸ (roughConjugateSubgroup D.Γ σ).comap L.subtype) :=
      (roughNativeOrbitSourceMetric D L σ).toUniformSpace.toTopologicalSpace
    ∃ K : NNReal, ∀ (t : ℝ), |t| ≤ R → ∀ F : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) →
      ∃ f : (L ⧸ (roughConjugateSubgroup D.Γ σ).comap L.subtype) → ℝ,
        LipschitzWith K f ∧
          (∀ x, |F (roughConjugateOrbitMap D.Γ L σ
            (nativeLieExponential (I := D.I) (G := D.G) (t • V)) x) - f x| ≤ ε) ∧
          (∀ x, |f x| ≤ B) := by
  letI := rough_native_residue_kernel_quotient_compact D.Γ S hS χ hχ hQ V hV j
  exact rough_native_orbit_lipschitz_approximation D _ _ V R B hB Lip hε

end Hindman168
