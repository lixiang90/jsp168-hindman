import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual smooth parameter families give uniform function AND first
curve-derivative limits on every compact interval and uniform bounds at
ALL sequence indices. Compactness comes from the convergent parameter
sequence itself; no equicontinuity or derivative oracle is an input. -/
namespace Hindman168
open Filter Set
open scoped Topology ContDiff
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def smoothParameterCurveDerivative (F : P × ℝ → E) (theta : P) (b : ℝ) : E :=
  fderiv ℝ (fun r : ℝ => F (theta,r)) b 1

omit [FiniteDimensional ℝ P] in
theorem smooth_parameter_curve_derivative_contDiff (F : P × ℝ → E) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × ℝ => smoothParameterCurveDerivative F p.1 p.2) := by
  have hJoint : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => F (p.1.1,p.2)) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact hJoint.fderiv_apply contDiff_snd contDiff_const (by simp)

omit [NormedSpace ℝ E] in
theorem smooth_parameter_compact_uniform_limit (F : P × ℝ → E) (hF : Continuous F)
    (theta : ℕ → P) (a : P) (htheta : Tendsto theta atTop (𝓝 a)) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n b => F (theta n,b)) (fun b => F (a,b)) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G (p : P) (b : K) : E := F (p,b)
  have hc : Continuous (fun x : P × K => G x.1 x.2) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := Continuous.tendstoUniformly G hc a
  intro U hU
  have he : ∀ᶠ n in atTop, ∀ b : K, (G a b,G (theta n) b) ∈ U :=
    htheta.eventually (hu U hU)
  exact he.mono (fun n hn b hb => hn ⟨b,hb⟩)

theorem smooth_parameter_compact_C1_limits (F : P × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (theta : ℕ → P) (a : P) (htheta : Tendsto theta atTop (𝓝 a)) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n b => F (theta n,b)) (fun b => F (a,b)) atTop K ∧
    TendstoUniformlyOn (fun n b => smoothParameterCurveDerivative F (theta n) b)
      (smoothParameterCurveDerivative F a) atTop K :=
  ⟨smooth_parameter_compact_uniform_limit F hF.continuous theta a htheta K hK,
    smooth_parameter_compact_uniform_limit _ (smooth_parameter_curve_derivative_contDiff F hF).continuous
      theta a htheta K hK⟩

omit [FiniteDimensional ℝ P] in
theorem smooth_parameter_compact_C1_bounds (F : P × ℝ → E) (hF : ContDiff ℝ ∞ F)
    (theta : ℕ → P) (a : P) (htheta : Tendsto theta atTop (𝓝 a)) (K : Set ℝ) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ∀ b ∈ K, ‖F (theta n,b)‖ ≤ B ∧
      ‖smoothParameterCurveDerivative F (theta n) b‖ ≤ B := by
  have hC : IsCompact (insert a (range theta) ×ˢ K) := htheta.isCompact_insert_range.prod hK
  obtain ⟨B0,hB0⟩ := hC.exists_bound_of_continuousOn hF.continuous.continuousOn
  obtain ⟨B1,hB1⟩ := hC.exists_bound_of_continuousOn
    (smooth_parameter_curve_derivative_contDiff F hF).continuous.continuousOn
  refine ⟨max 0 (max B0 B1),le_max_left _ _,?_⟩
  intro n b hb
  have hp : (theta n,b) ∈ insert a (range theta) ×ˢ K := ⟨mem_insert_of_mem _ (mem_range_self n),hb⟩
  exact ⟨(hB0 _ hp).trans ((le_max_left B0 B1).trans (le_max_right _ _)),
    (hB1 _ hp).trans ((le_max_right B0 B1).trans (le_max_right _ _))⟩

end Hindman168
