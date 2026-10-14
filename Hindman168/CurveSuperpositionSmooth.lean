import Hindman168.CurveSuperpositionRemainder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Higher smoothness of the original continuous-curve superposition.
An actual C2 field produces the genuine pointwise derivative at every
nearby curve. Induction lifts finite orders with one order of slack;
therefore a smooth original field gives a smooth curve-space map. -/

universe u v

namespace Hindman168
open Set Metric Filter Topology
open scoped ContDiff

variable {K : Type v} [TopologicalSpace K] [CompactSpace K]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem curveSuperposition_eventually_hasFDerivAt {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) :
    ∀ᶠ α : C(K, E) in 𝓝 (ContinuousMap.const K x),
      HasFDerivAt (curveSuperposition f)
        (curveApplyLinear (curveSuperposition (fderiv ℝ f) α)) α := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  obtain ⟨C, U, hU, hLip⟩ := (hd.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  have he : ∀ᶠ z in 𝓝 x, HasFDerivAt f (fderiv ℝ f z) z :=
    (hf.eventually (by norm_num)).mono (fun z hz => (hz.differentiableAt (by norm_num)).hasFDerivAt)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (inter_mem hU he)
  have hD (z : E) (hz : z ∈ ball x r) : HasFDerivAt f (fderiv ℝ f z) z := (hrs hz).2
  have hL := hLip.mono (fun z hz => (hrs hz).1)
  filter_upwards [ball_mem_nhds (ContinuousMap.const K x) (by positivity : 0 < r / 2)] with α hα
  apply curveSuperposition_hasFDerivAt_ball hr hD hL α
  intro t
  exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist t) hα

 theorem curveSuperposition_contDiffAt_loss_one (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ (n + 1) f x) :
    ContDiffAt ℝ n (curveSuperposition (K := K) f) (ContinuousMap.const K x) := by
  induction n generalizing F with
  | zero =>
    have hs := curveSuperposition_hasStrictFDerivAt_const (K := K)
      (hf.hasStrictFDerivAt (by norm_num))
    obtain ⟨C, U, hU, hLip⟩ := hs.exists_lipschitzOnWith
    exact contDiffAt_zero.mpr ⟨U, hU, hLip.continuousOn⟩
  | succ n ih =>
    have hd : ContDiffAt ℝ (n + 1) (fderiv ℝ f) x := hf.fderiv_right (by simp)
    have hs := ih hd
    have ho := (curvePointwiseOperator_contDiff (K := K) (E := E) (F := F) n).contDiffAt.comp
      (ContinuousMap.const K x) hs
    have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_cast; omega)
    obtain ⟨U, hU, hDU⟩ := (curveSuperposition_eventually_hasFDerivAt (K := K) hf2).exists_mem
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun α => curveApplyLinear (curveSuperposition (fderiv ℝ f) α), ⟨U, hU, hDU⟩, ?_⟩
    convert! ho using 1

 theorem curveSuperposition_contDiffAt_smooth {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (curveSuperposition (K := K) f) (ContinuousMap.const K x) := by
  apply contDiffAt_infty.mpr
  intro n
  apply curveSuperposition_contDiffAt_loss_one n
  simpa only [Nat.cast_add, Nat.cast_one] using contDiffAt_infty.mp hf (n + 1)

end Hindman168
