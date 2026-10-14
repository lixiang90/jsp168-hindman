import Hindman168.RoughNativeActionFreezing
import Hindman168.RoughNativeKernelFactorization

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_ordered_factor_freezing {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (V : D.E) (B K : ℝ) (hK : 0 ≤ K) (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith L F →
      ∀ (a b m : ℝ) (g : D.G), |a| ≤ B → |b| ≤ B → |a - b| ≤ K * r →
        |F (QuotientGroup.mk g) - F (QuotientGroup.mk
          (nativeLieExponential (I := D.I) (G := D.G) (b • V) *
            roughNativeKernelFactor (I := D.I) V a m g *
            nativeLieExponential (I := D.I) (G := D.G) (m • V)))| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨r, hr, hfreeze⟩ := rough_native_scalar_test_freezing D V B K hK L hε
  refine ⟨r, hr, ?_⟩
  intro F hF a b m g ha hb hab
  let Q := roughNativeKernelFactor (I := D.I) V a m g
  let R := nativeLieExponential (I := D.I) (G := D.G) (m • V)
  have h := hfreeze F hF a b (QuotientGroup.mk (Q * R)) ha hb hab
  have he : nativeLieExponential (I := D.I) (G := D.G) (a • V) * (Q * R) = g :=
    (mul_assoc _ _ _).symm.trans (rough_native_kernel_factorization V a m g).symm
  change |F (QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G) (a • V) * (Q * R))) -
    F (QuotientGroup.mk (nativeLieExponential (I := D.I) (G := D.G) (b • V) * (Q * R)))| < ε at h
  rw [he] at h
  simpa only [mul_assoc] using h

end Hindman168
