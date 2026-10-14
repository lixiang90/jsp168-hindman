import Hindman168.NativeSmoothBinomialVelocity
import Hindman168.NativeSmoothGroupMapLimits

/-! Complete native smooth-curve conclusion in original group topology
and genuine left-trivialized manifold derivatives. The compact-open limit,
the smooth limiting map, uniform body-velocity limits and ALL-index bounds
come from the SAME actual finite parameter family and factor sequence. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSequentialBodyVelocityLimit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (c : ℕ → D.G)
    (as : List (NativeSequentialBinomialFactor D)) : Prop :=
  ∃ h : C(ℝ,D.G), ContMDiff 𝓘(ℝ) D.I ∞ h ∧
    (∀ n, ContMDiff 𝓘(ℝ) D.I ∞ (nativeSequentialSmoothGroupCurve D L c as n)) ∧
    Tendsto (nativeSequentialSmoothGroupMaps D L c as) atTop (𝓝 h) ∧
    ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n => nativeCurveBodyVelocity D (nativeSequentialSmoothGroupCurve D L c as n))
        (nativeCurveBodyVelocity D h) atTop K ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∀ b ∈ K, ‖nativeSequentialSmoothLogCurve D L c as n b‖ ≤ B ∧
        ‖nativeCurveBodyVelocity D (nativeSequentialSmoothGroupCurve D L c as n) b‖ ≤ B

theorem native_sequential_body_velocity_limits {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D))
    (hCoeffs : ∀ a ∈ as, ∃ z : ℝ,
      Tendsto (fun n => (L n)^a.order * a.realCoefficient n) atTop (𝓝 z)) :
    NativeSequentialBodyVelocityLimit D L c as := by
  classical
  choose z hz using (fun i : Fin as.length => hCoeffs (as.get i) (List.get_mem as i))
  let theta : ℕ → NativeSmoothBinomialParameter D as.length := nativeSequentialSmoothParameter D L c as
  let a : NativeSmoothBinomialParameter D as.length :=
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) cLimit,0,z)
  let F : NativeSmoothBinomialParameter D as.length × ℝ → D.E := fun p =>
    nativeSmoothBinomialFamilyLog D (fun i => (as.get i).order) (fun i => (as.get i).vector) p.1 p.2
  let V : NativeSmoothBinomialParameter D as.length × ℝ → D.E := fun p =>
    nativeSmoothBinomialFamilyVelocity D (fun i => (as.get i).order) (fun i => (as.get i).vector) p.1 p.2
  let h : C(ℝ,D.G) := nativeSmoothBinomialGroupMaps D
    (fun i => (as.get i).order) (fun i => (as.get i).vector) a
  have hF : ContDiff ℝ ∞ F := native_smooth_binomial_family_contDiff D _ _
  have hV : ContDiff ℝ ∞ V := native_smooth_binomial_velocity_contDiff D _ _
  have htheta : Tendsto theta atTop (𝓝 a) := native_sequential_smooth_parameter_limit D L hL c cLimit hc as z hz
  have hFixed (p : NativeSmoothBinomialParameter D as.length) : ContDiff ℝ ∞ (fun b => F (p,b)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hSeqVelocity (n : ℕ) : nativeCurveBodyVelocity D (nativeSequentialSmoothGroupCurve D L c as n) =
      (fun b => V (theta n,b)) := native_sequential_body_velocity_parameter_identity D L c as n
  have hLimitVelocity : nativeCurveBodyVelocity D h = (fun b => V (a,b)) :=
    funext (fun b => native_curve_body_velocity_exponential D (fun r => F (a,r)) (hFixed a) b)
  refine ⟨h,?_,?_,?_,?_⟩
  · exact (nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp (hFixed a).contMDiff
  · intro n
    have he : nativeSequentialSmoothGroupCurve D L c as n = fun b =>
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (F (theta n,b)) :=
      funext (fun b => (native_sequential_smooth_parameter_actual_product D L c as n b).symm)
    rw [he]
    exact (nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp (hFixed (theta n)).contMDiff
  · exact native_sequential_smooth_group_maps_limit D L hL c cLimit hc as z hz
  · intro K hK
    have hUniform := smooth_parameter_compact_uniform_limit V hV.continuous theta a htheta K hK
    have hBoundsF := smooth_parameter_compact_C1_bounds F hF theta a htheta K hK
    have hCompact : IsCompact (insert a (range theta) ×ˢ K) := htheta.isCompact_insert_range.prod hK
    obtain ⟨B0,_,hB0⟩ := hBoundsF
    obtain ⟨B1,hB1⟩ := hCompact.exists_bound_of_continuousOn hV.continuous.continuousOn
    refine ⟨?_,max 0 (max B0 B1),le_max_left _ _,?_⟩
    · have he : (fun n => nativeCurveBodyVelocity D (nativeSequentialSmoothGroupCurve D L c as n)) =
        (fun n b => V (theta n,b)) := funext hSeqVelocity
      rw [he,hLimitVelocity]
      exact hUniform
    · intro n b hb
      have hp : (theta n,b) ∈ insert a (range theta) ×ˢ K := ⟨mem_insert_of_mem _ (mem_range_self n),hb⟩
      have hLog := native_sequential_smooth_curve_parameter_identity D L c as n
      rw [hLog,hSeqVelocity n]
      exact ⟨((hB0 n b hb).1).trans ((le_max_left B0 B1).trans (le_max_right _ _)),
        (hB1 _ hp).trans ((le_max_right B0 B1).trans (le_max_right _ _))⟩

end Hindman168
