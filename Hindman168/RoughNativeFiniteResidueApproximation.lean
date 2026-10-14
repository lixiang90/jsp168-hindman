import Hindman168.RoughNativeKernelApproximation
import Hindman168.RoughFiniteFamilyApproximation

namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_finite_residue_lipschitz_approximation {s : ℕ} {ι : Type*} [Fintype ι]
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hV : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (residue : ι → ℤ) (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    let L := nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ)
    let σ := fun j => nativeLieExponential (I := D.I) (G := D.G) ((residue j : ℝ) • V)
    let X := fun j => L ⧸ (roughConjugateSubgroup D.Γ (σ j)).comap L.subtype
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace (X j) := fun j => roughNativeOrbitSourceMetric D L (σ j)
    letI : ∀ j, TopologicalSpace (X j) := fun j =>
      (roughNativeOrbitSourceMetric D L (σ j)).toUniformSpace.toTopologicalSpace
    ∃ K : NNReal, ∀ (j : ι) (t : ℝ), |t| ≤ R → ∀ F : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) → ∃ f : X j → ℝ,
        LipschitzWith K f ∧
          (∀ x, |F (roughConjugateOrbitMap D.Γ L (σ j)
            (nativeLieExponential (I := D.I) (G := D.G) (t • V)) x) - f x| ≤ ε) ∧
          (∀ x, |f x| ≤ B) := by
  let L := nativeLieSubalgebraSubgroup (E := D.E) (nativeLieCharacterKernel S χ hχ)
  let σ := fun j => nativeLieExponential (I := D.I) (G := D.G) ((residue j : ℝ) • V)
  let X := fun j => L ⧸ (roughConjugateSubgroup D.Γ (σ j)).comap L.subtype
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace (X j) := fun j => roughNativeOrbitSourceMetric D L (σ j)
  letI : ∀ j, TopologicalSpace (X j) := fun j =>
    (roughNativeOrbitSourceMetric D L (σ j)).toUniformSpace.toTopologicalSpace
  letI : ∀ j, CompactSpace (X j) := fun j => by
    letI := rough_native_residue_kernel_quotient_compact D.Γ S hS χ hχ hQ V hV (residue j)
    exact rough_native_orbit_source_metric_compact D L (σ j)
  letI : ∀ j, Nonempty (X j) := fun _ => inferInstance
  exact rough_finite_family_lipschitz_approximation X _
    (fun j => rough_native_scalar_orbit_continuous D L (σ j) V) R B hB Lip hε

end Hindman168
