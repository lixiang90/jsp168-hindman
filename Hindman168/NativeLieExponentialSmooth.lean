import Hindman168.NativeLieExponentialSmoothAtZero
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Global smoothness of the original native exponential. For each
finite order a genuine neighbourhood of zero is smooth. Scaling a
given vector into this neighbourhood and the proved single-parameter
power identity extend that order to every vector. No additive
exponential law for different vectors or global inverse is assumed. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieGroup_pow_contMDiff (m : ℕ) :
    ContMDiff I I ∞ (fun g : G => g ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using (contMDiff_const : ContMDiff I I ∞ (fun _ : G => (1 : G)))
  | succ m ih =>
    have hh : ContMDiff I I ∞ (fun g : G => g ^ m * g) := by
      convert! ih.mul (contMDiff_id : ContMDiff I I ∞ (fun g : G => g)) using 1
    simpa only [pow_succ] using hh

 theorem nativeLieExponential_contMDiff :
    ContMDiff 𝓘(ℝ, E) I ∞ (fun v : E => nativeLieExponential (I := I) (G := G) v) := by
  apply contMDiff_infty.mpr
  intro n v₀
  have h0 := contMDiffAt_infty.mp
    (nativeLieExponential_contMDiffAt_smooth_zero (I := I) (G := G)) n
  have he := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (n : ℕ∞ω) ≠ ∞)).mp h0
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (div_pos hr (by positivity : (0 : ℝ) < ‖v₀‖ + 1))
  let c : ℝ := 1 / (k + 1 : ℝ)
  have hc : 0 < c := by positivity
  have hcmul : c * (‖v₀‖ + 1) < r :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖v₀‖ + 1)).mp hk
  have hball : c • v₀ ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    nlinarith
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (fun w : E => c • w) v₀ :=
    (contDiffAt_const.smul contDiffAt_id).contMDiffAt
  have hpower : ContMDiff I I n (fun g : G => g ^ (k + 1)) :=
    (nativeLieGroup_pow_contMDiff (I := I) (G := G) (k + 1)).of_le (mod_cast le_top)
  have hp := hpower.contMDiffAt.comp v₀ ((hrs hball).comp v₀ hs)
  have heq : (fun w : E => nativeLieExponential (I := I) (G := G) (c • w) ^ (k + 1)) =
      (fun w : E => nativeLieExponential (I := I) (G := G) w) := by
    funext w
    calc
      nativeLieExponential (I := I) (G := G) (c • w) ^ (k + 1) =
          lieOneParameterCurve (I := I) (G := G) w c ^ (k + 1) :=
        congrArg (fun g : G => g ^ (k + 1)) (nativeLieExponential_smul w c)
      _ = lieOneParameterCurve (I := I) (G := G) w ((k + 1 : ℝ) * c) :=
        by simpa only [Nat.cast_add, Nat.cast_one] using
          (lieOneParameterCurve_nat_mul (I := I) (G := G) w (k + 1) c).symm
      _ = nativeLieExponential (I := I) (G := G) w := by
        have hkc : (k + 1 : ℝ) * c = 1 := mul_one_div_cancel (by positivity)
        rw [hkc]
        rfl
  change ContMDiffAt 𝓘(ℝ, E) I n
    (fun w : E => nativeLieExponential (I := I) (G := G) (c • w) ^ (k + 1)) v₀ at hp
  rw [heq] at hp
  exact hp

 theorem lieOneParameterCurve_joint_contMDiff :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : E × ℝ => lieOneParameterCurve (I := I) (G := G) p.1 p.2) := by
  have hs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : E × ℝ => p.2 • p.1) := contMDiff_snd.smul contMDiff_fst
  have h := (nativeLieExponential_contMDiff (I := I) (G := G)).comp hs
  apply h.congr
  intro p
  exact (nativeLieExponential_smul p.1 p.2).symm

 theorem lieInvariantFlow_joint_contMDiff :
    ContMDiff (I.prod (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ))) I ∞
      (fun p : G × (E × ℝ) =>
        p.1 * lieOneParameterCurve (I := I) (G := G) p.2.1 p.2.2) :=
  contMDiff_fst.mul ((lieOneParameterCurve_joint_contMDiff (I := I) (G := G)).comp contMDiff_snd)

end Hindman168
