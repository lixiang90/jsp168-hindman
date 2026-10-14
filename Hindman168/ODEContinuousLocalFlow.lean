import Mathlib.Analysis.ODE.ExistUnique

/-! Continuous local flows obtained from actual C1 vector fields.
The flow and its common interval are constructed by Picard-Lindelof;
continuous dependence is not an input hypothesis. -/

namespace Hindman168
open Set Metric Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem contDiffAt_exists_continuous_local_flow
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t) ∧
      ContinuousOn α (closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα, hc⟩ :=
    (hpl t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, ε, hε, α, ?_, ?_⟩
  · intro x hx
    refine ⟨(hα x hx).1, fun t ht => ?_⟩
    exact (hα x hx).2 t (Ioo_subset_Icc_self ht) |>.hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  · exact hc.mono (prod_subset_prod_right Ioo_subset_Icc_self)

 theorem contDiffAt_exists_continuous_open_local_flow
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ α : E × ℝ → E,
      (∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t) ∧
      ContinuousOn α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r, hr, ε, hε, α, hα, hc⟩ :=
    contDiffAt_exists_continuous_local_flow hf t₀
  exact ⟨r, hr, ε, hε, α, fun x hx => hα x (ball_subset_closedBall hx),
    hc.mono (prod_subset_prod_left ball_subset_closedBall)⟩

 theorem contDiffAt_exists_continuous_local_flow_mem
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ)
    {u : Set E} (hu : u ∈ 𝓝 x₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ α : E × ℝ → E,
      (∀ x ∈ ball x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt (fun s => α (x, s)) (f (α (x, t))) t ∧ α (x, t) ∈ u) ∧
      ContinuousOn α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨r, hr, ε, hε, α, hα, hc⟩ :=
    contDiffAt_exists_continuous_open_local_flow hf t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hcont : ContinuousAt α (x₀, t₀) :=
    (hc (x₀, t₀) ⟨hx₀, ht₀⟩).continuousAt
      ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hx₀, ht₀⟩)
  have heq : α (x₀, t₀) = x₀ := (hα x₀ hx₀).1
  have hv : α ⁻¹' u ∈ 𝓝 (x₀, t₀) := hcont.preimage_mem_nhds (heq.symm ▸ hu)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨min r δ, lt_min hr hδ, min ε δ, lt_min hε hδ, α, ?_, ?_⟩
  · intro x hx
    have hxr : x ∈ ball x₀ r := ball_subset_ball (min_le_left r δ) hx
    refine ⟨(hα x hxr).1, fun t ht => ?_⟩
    have hte : t ∈ Ioo (t₀ - ε) (t₀ + ε) := by
      constructor <;> linarith [min_le_left ε δ, ht.1, ht.2]
    refine ⟨(hα x hxr).2 t hte, hsub ?_⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨lt_of_lt_of_le hx (min_le_right r δ), ?_⟩
    change dist t t₀ < δ
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_right ε δ, ht.1, ht.2]
  · apply hc.mono
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨ball_subset_ball (min_le_left r δ) hx, ?_⟩
    constructor <;> linarith [min_le_left ε δ, ht.1, ht.2]

end Hindman168
