import Hindman168.CompactSequentialParameterFreezing
import Hindman168.NativeSequentialSmoothLimits
import Hindman168.NativeRationalLayerOrbitObservables

/-! Uniform freezing of the actual original smooth left factors on the
original compact quotient. The group action is only assumed continuous;
the required modulus is derived from the genuine parameter convergence. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_metric_group_action_continuous {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun z : D.G × (D.G ⧸ D.Γ) => z.1 • z.2) := by
  let P (t : TopologicalSpace (D.G ⧸ D.Γ)) : Prop :=
    letI := t
    Continuous (fun z : D.G × (D.G ⧸ D.Γ) => z.1 • z.2)
  have hn : P (QuotientGroup.instTopologicalSpace D.Γ) := continuous_fst.smul continuous_snd
  exact Eq.mp (congrArg P (nativeNilmanifold_metric_topology D)) hn

theorem native_parameter_action_freezing {s : ℕ} {P : Type*} [UniformSpace P]
    [WeaklyLocallyCompactSpace P]
    (D : NativeNilmanifoldData.{u} s) (g : P × ℝ → D.G) (hg : Continuous g)
    (theta : ℕ → P) (a : P) (htheta : Tendsto theta atTop (𝓝 a))
    (beta ε : ℝ) (hε : 0 < ε) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, ∀ t : ℝ, |t-beta| < r →
      ∀ x : D.G ⧸ D.Γ, dist (g (theta n,t) • x) (g (a,beta) • x) < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  exact compact_sequential_parameter_freezing
    (fun z : (P × ℝ) × (D.G ⧸ D.Γ) => g z.1 • z.2)
    ((native_metric_group_action_continuous D).comp ((hg.comp continuous_fst).prodMk continuous_snd))
    theta a htheta beta ε hε

theorem native_sequential_smooth_left_action_freezing {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D))
    (hCoeffs : ∀ a ∈ as, ∃ z : ℝ,
      Tendsto (fun n => (L n)^a.order * a.realCoefficient n) atTop (𝓝 z)) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ h : ℝ → D.G, ContMDiff 𝓘(ℝ) D.I ∞ h ∧
      ∀ beta ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
        ∀ t : ℝ, |t-beta| < r → ∀ x : D.G ⧸ D.Γ,
          dist ((c n * nativeSequentialFactorsLeft D n (L n*t) as) • x) (h beta • x) < ε := by
  classical
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  choose z hz using (fun i : Fin as.length => hCoeffs (as.get i) (List.get_mem as i))
  let theta := nativeSequentialSmoothParameter D L c as
  let a : NativeSmoothBinomialParameter D as.length :=
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,0,z)
  let G : NativeSmoothBinomialParameter D as.length × ℝ → D.E := fun v =>
    nativeSmoothBinomialFamilyLog D (fun i => (as.get i).order) (fun i => (as.get i).vector) v.1 v.2
  let g : NativeSmoothBinomialParameter D as.length × ℝ → D.G := fun v =>
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (G v)
  have hG : ContDiff ℝ ∞ G := native_smooth_binomial_family_contDiff D _ _
  have hg : Continuous g := (nativeLieExponential_continuous (E := D.E) (I := D.I) (G := D.G)).comp hG.continuous
  have htheta : Tendsto theta atTop (𝓝 a) := native_sequential_smooth_parameter_limit D L hL c cLimit hc as z hz
  refine ⟨fun b => g (a,b),?_,?_⟩
  · exact (nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp
      (hG.comp (contDiff_const.prodMk contDiff_id)).contMDiff
  · intro beta ε hε
    obtain ⟨r,hr,h⟩ := native_parameter_action_freezing D g hg theta a htheta beta ε hε
    refine ⟨r,hr,?_⟩
    filter_upwards [h] with n hn
    intro t ht x
    have he : g (theta n,t) = c n * nativeSequentialFactorsLeft D n (L n*t) as :=
      native_sequential_smooth_parameter_actual_product D L c as n t
    rw [← he]
    exact hn t ht x

end Hindman168
