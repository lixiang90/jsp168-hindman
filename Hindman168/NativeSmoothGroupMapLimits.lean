import Hindman168.NativeSmoothFactorParameterization
import Mathlib.Topology.CompactOpen

/-! Convergence in the ACTUAL original group's compact-open topology.
Currying the genuine continuous finite parameter family avoids inventing a
metric or uniform structure on the original native group. Every bundled
sequence map is proved identical to the actual scaled left product. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSmoothBinomialGroupMaps {s : ℕ} {N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (order : Fin N → ℕ) (vector : Fin N → D.E) :
    C(NativeSmoothBinomialParameter D N,C(ℝ,D.G)) :=
  (⟨fun p : NativeSmoothBinomialParameter D N × ℝ => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (nativeSmoothBinomialFamilyLog D order vector p.1 p.2),
    (nativeLieExponential_continuous (E := D.E) (I := D.I) (G := D.G)).comp
      (native_smooth_binomial_family_contDiff D order vector).continuous⟩ : C(NativeSmoothBinomialParameter D N × ℝ,D.G)).curry

noncomputable def nativeSequentialSmoothGroupMaps {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) : C(ℝ,D.G) :=
  nativeSmoothBinomialGroupMaps D (fun i => (as.get i).order) (fun i => (as.get i).vector)
    (nativeSequentialSmoothParameter D L c as n)

theorem native_sequential_smooth_group_maps_apply {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) :
    nativeSequentialSmoothGroupMaps D L c as n b = c n * nativeSequentialFactorsLeft D n (L n*b) as :=
  native_sequential_smooth_parameter_actual_product D L c as n b

theorem native_sequential_smooth_group_maps_limit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D)) (z : Fin as.length → ℝ)
    (hz : ∀ i, Tendsto (fun n => (L n)^(as.get i).order * (as.get i).realCoefficient n) atTop (𝓝 (z i))) :
    Tendsto (nativeSequentialSmoothGroupMaps D L c as) atTop
      (𝓝 (nativeSmoothBinomialGroupMaps D (fun i => (as.get i).order) (fun i => (as.get i).vector)
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,(0 : ℝ),z))) :=
  ((nativeSmoothBinomialGroupMaps D _ _).continuous.tendsto _).comp
    (native_sequential_smooth_parameter_limit D L hL c cLimit hc as z hz)

end Hindman168
