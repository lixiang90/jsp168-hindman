import Hindman168.RoughNativePackagedResidueApproximation
import Hindman168.RoughConjugateResidueTest

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_residue_product_approximation {s : ℕ} {ι : Type*} [Fintype ι]
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
    let σ := fun j => nativeLieExponential (I := D.I) (G := D.G) ((residue j : ℝ) • V)
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ j, MetricSpace ((N j).G ⧸ (N j).Γ) := fun j => (N j).metric
    letI : ∀ j, TopologicalSpace ((N j).G ⧸ (N j).Γ) := fun j =>
      (N j).metric.toUniformSpace.toTopologicalSpace
    ∃ K : NNReal, ∀ (j : ι) (b : ℝ), |b| ≤ R → ∀ F : (D.G ⧸ D.Γ) → ℝ,
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) → ∃ f : (N j).G ⧸ (N j).Γ → ℝ,
        LipschitzWith K f ∧ (∀ x, |f x| ≤ B) ∧
          ∀ (h : (N j).G) (right : D.G),
            (QuotientGroup.mk right : D.G ⧸ D.Γ) = QuotientGroup.mk (σ j) →
            |F (QuotientGroup.mk
              (nativeLieExponential (I := D.I) (G := D.G) (b • V)*h.val*right))-
              f (QuotientGroup.mk h)| ≤ ε := by
  intro N σ
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ j, MetricSpace ((N j).G ⧸ (N j).Γ) := fun j => (N j).metric
  letI : ∀ j, TopologicalSpace ((N j).G ⧸ (N j).Γ) := fun j =>
    (N j).metric.toUniformSpace.toTopologicalSpace
  obtain ⟨K, hk⟩ := rough_native_packaged_residue_approximation D S hS χ hχ hQ V hVr residue R B hB Lip hε
  refine ⟨K, ?_⟩
  intro j b hb F hF hbound
  obtain ⟨f, hf, he, hfb⟩ := hk j b hb F hF hbound
  refine ⟨f, hf, hfb, ?_⟩
  intro h right hcoset
  exact rough_conjugate_residue_test D.Γ _ (σ j)
    (nativeLieExponential (I := D.I) (G := D.G) (b • V)) right h hcoset F f ε he

end Hindman168
