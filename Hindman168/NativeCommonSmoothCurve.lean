import Hindman168.NativeSmoothActionFreezing

/-! One explicit smooth-action limit witness can be shared by point and cube laws.
Its existence is proved from the actual sequential factors, not postulated. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSmoothActionLimit {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : ℕ → ℝ) (c : ℕ → D.G) (as : List (NativeSequentialBinomialFactor D))
    (h : ℝ → D.G) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
    ∀ t : ℝ, |t-beta| < r → ∀ x : D.G ⧸ D.Γ,
      dist ((c n * nativeSequentialFactorsLeft D n (L n*t) as) • x) (h beta • x) < ε

theorem native_common_smooth_curve {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D))
    (hCoeffs : ∀ a ∈ as, ∃ z : ℝ,
      Tendsto (fun n => (L n)^a.order * a.realCoefficient n) atTop (𝓝 z)) :
    ∃ h : ℝ → D.G, ContMDiff 𝓘(ℝ) D.I ∞ h ∧ NativeSmoothActionLimit D L c as h :=
  native_sequential_smooth_left_action_freezing D L hL c cLimit hc as hCoeffs

end Hindman168
