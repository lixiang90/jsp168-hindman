import Hindman168.RoughCompactParameterFreezing
import Hindman168.NativeMetricMaskModelTesting

namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_scalar_action_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (V : D.E) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun p : ℝ × (D.G ⧸ D.Γ) =>
      nativeLieExponential (I := D.I) (G := D.G) (p.1 • V) • p.2) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let f : ℝ × (D.G ⧸ D.Γ) → D.G ⧸ D.Γ := fun p =>
    nativeLieExponential (I := D.I) (G := D.G) (p.1 • V) • p.2
  let P (t : TopologicalSpace (D.G ⧸ D.Γ)) : Prop :=
    letI := t
    Continuous f
  have hn : P (QuotientGroup.instTopologicalSpace D.Γ) := by
    letI : TopologicalSpace (D.G ⧸ D.Γ) := QuotientGroup.instTopologicalSpace D.Γ
    have hs : Continuous (fun p : ℝ × (D.G ⧸ D.Γ) => (p.1 • V : D.E)) :=
      continuous_fst.smul continuous_const
    have he : Continuous (fun p : ℝ × (D.G ⧸ D.Γ) =>
        nativeLieExponential (I := D.I) (G := D.G) (p.1 • V)) :=
      (nativeLieExponential_continuous (E := D.E) (I := D.I) (G := D.G)).comp hs
    exact he.smul continuous_snd
  exact Eq.mp (congrArg P (nativeNilmanifold_metric_topology D)) hn

theorem rough_native_scalar_test_freezing {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (V : D.E) (B K : ℝ) (hK : 0 ≤ K) (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ ∀ F : (D.G ⧸ D.Γ) → ℝ, LipschitzWith L F →
      ∀ (a b : ℝ) (x : D.G ⧸ D.Γ), |a| ≤ B → |b| ≤ B → |a - b| ≤ K * r →
      |F (nativeLieExponential (I := D.I) (G := D.G) (a • V) • x) -
        F (nativeLieExponential (I := D.I) (G := D.G) (b • V) • x)| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := Eq.mp
    (congrArg (fun t => @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D))
    D.quotientCompact
  exact rough_compact_lipschitz_test_freezing _ (rough_native_scalar_action_continuous D V) B K hK L hε

end Hindman168
