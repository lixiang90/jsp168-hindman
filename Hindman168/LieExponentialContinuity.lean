import Hindman168.LieFrozenParameterFlow
import Hindman168.ManifoldContinuousLocalFlow
import Mathlib.Algebra.Order.Archimedean.Basic

/-! General native exponential continuity, proved from the constructed
continuous local flow of the actual frozen-parameter field. Uniqueness
identifies that flow with the original exponential curves. The group
law then extends local parameter continuity to time one. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G] [T2Space G]

 theorem lieOneParameterCurve_continuousAt_local_parameter (v₀ : E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (-ε) ε,
      ContinuousAt (fun v : E => lieOneParameterCurve (I := I) (G := G) v t) v₀ := by
  obtain ⟨U, hU, ε, hε, α, hα, hc⟩ :=
    manifold_contMDiffAt_exists_continuous_local_flow
      (I := 𝓘(ℝ, E).prod I) (x₀ := (v₀, (1 : G)))
      lieFrozenParameterField_contMDiff_one.contMDiffAt (0 : ℝ)
  have ht₀ : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
  have hV : (fun v : E => (v, (1 : G))) ⁻¹' U ∈ 𝓝 v₀ :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU
  have heq (v : E) (hv : (v, (1 : G)) ∈ U) (t : ℝ)
      (ht : t ∈ Ioo (0 - ε) (0 + ε)) :
      α ((v, (1 : G)), t) = (v, lieOneParameterCurve (I := I) (G := G) v t) := by
    apply isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (I := 𝓘(ℝ, E).prod I) ht₀ lieFrozenParameterField_contMDiff_one
      (hα _ hv).2 ((lieFrozenParameterCurve_integral v).isMIntegralCurveOn _) ?_ ht
    exact (hα _ hv).1.trans (by rw [lieOneParameterCurve_zero])
  refine ⟨ε, hε, fun t ht => ?_⟩
  have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by simpa only [zero_sub, zero_add] using ht
  have hc₀ : ContinuousAt α ((v₀, (1 : G)), t) :=
    (hc _ ⟨mem_of_mem_nhds hU, ht'⟩).continuousAt
      (prod_mem_nhds hU (Ioo_mem_nhds ht'.1 ht'.2))
  have hφ : Continuous (fun v : E => ((v, (1 : G)), t)) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hp : ContinuousAt (fun v : E => (α ((v, (1 : G)), t)).2) v₀ :=
    (hc₀.comp (f := fun v : E => ((v, (1 : G)), t)) hφ.continuousAt).snd
  apply hp.congr
  filter_upwards [hV] with v hv
  exact congrArg Prod.snd (heq v hv t ht')

 theorem lieOneParameterCurve_nat_mul (v : E) (n : ℕ) (t : ℝ) :
    lieOneParameterCurve (I := I) (G := G) v ((n : ℝ) * t) =
      (lieOneParameterCurve (I := I) (G := G) v t) ^ n := by
  have h := congrArg Additive.toMul (map_nsmul (lieOneParameterHom (I := I) (G := G) v) n t)
  change lieOneParameterCurve (I := I) (G := G) v (n • t) =
    (lieOneParameterCurve (I := I) (G := G) v t) ^ n at h
  simpa only [nsmul_eq_mul] using h

 theorem nativeLieExponential_continuous :
    Continuous (nativeLieExponential (I := I) (G := G) : E → G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨ε, hε, hc⟩ := lieOneParameterCurve_continuousAt_local_parameter (I := I) (G := G) v₀
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hs : (1 / (n + 1 : ℝ)) ∈ Ioo (-ε) ε := ⟨lt_trans (neg_neg_of_pos hε) (by positivity), hn⟩
  have hp := (hc _ hs).pow (n + 1)
  have heq : (fun v : E => lieOneParameterCurve (I := I) (G := G) v
      (1 / (n + 1 : ℝ)) ^ (n + 1)) = nativeLieExponential (I := I) (G := G) := by
    funext v
    have h := lieOneParameterCurve_nat_mul (I := I) (G := G) v (n + 1)
      (1 / (n + 1 : ℝ))
    simp only [Nat.cast_add, Nat.cast_one] at h
    rw [mul_one_div_cancel (by positivity : (n + 1 : ℝ) ≠ 0)] at h
    exact h.symm
  change ContinuousAt (fun v : E => lieOneParameterCurve (I := I) (G := G) v
    (1 / (n + 1 : ℝ)) ^ (n + 1)) v₀ at hp
  rw [heq] at hp
  exact hp

 theorem lieOneParameterCurve_joint_continuous :
    Continuous (fun p : E × ℝ => lieOneParameterCurve (I := I) (G := G) p.1 p.2) := by
  have h := (nativeLieExponential_continuous (I := I) (G := G)).comp
    (show Continuous (fun p : E × ℝ => p.2 • p.1) from
      continuous_snd.smul continuous_fst)
  have heq : (fun p : E × ℝ => nativeLieExponential (I := I) (G := G) (p.2 • p.1)) =
      (fun p : E × ℝ => lieOneParameterCurve (I := I) (G := G) p.1 p.2) := by
    funext p
    exact nativeLieExponential_smul p.1 p.2
  exact heq ▸ h

 theorem lieInvariantFlow_joint_continuous :
    Continuous (fun p : G × (E × ℝ) =>
      p.1 * lieOneParameterCurve (I := I) (G := G) p.2.1 p.2.2) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  exact continuous_fst.mul ((lieOneParameterCurve_joint_continuous (I := I) (G := G)).comp continuous_snd)

end Hindman168
