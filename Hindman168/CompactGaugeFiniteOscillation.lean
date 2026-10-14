import Hindman168.CompactGaugeUniformMesh
import Mathlib.Analysis.Complex.Basic

/-! A common finite mesh for a positive local gauge and a finite continuous
observable family. All choices precede subsequent sequence limits. -/
namespace Hindman168
open Filter Set Metric
open scoped Topology

theorem compact_gauge_finite_oscillation {R : Type*} [Finite R]
    (radius : Icc (0 : ℝ) 1 → ℝ) (hr : ∀ x, 0 < radius x)
    (g : R → ℝ → ℂ) (hg : ∀ r, Continuous (g r)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ tag : Fin N → Icc (0 : ℝ) 1,
      ∀ i : Fin N, ∀ t ∈ Icc ((i.val : ℝ)/N) (((i.val : ℝ)+1)/N),
        |t-(tag i : ℝ)| < radius (tag i) ∧ ∀ r, ‖g r t-g r (tag i)‖ < ε := by
  have hδ (x : Icc (0 : ℝ) 1) : ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, |t-(x : ℝ)| < δ → ∀ r, ‖g r t-g r x‖ < ε := by
    have he : ∀ᶠ t in 𝓝 (x : ℝ), ∀ r, ‖g r t-g r x‖ < ε :=
      Filter.eventually_all.mpr (fun r => by
        have ho : IsOpen {t : ℝ | ‖g r t-g r x‖ < ε} :=
          isOpen_lt ((hg r).sub continuous_const).norm continuous_const
        exact ho.mem_nhds (by simpa only [mem_setOf_eq, sub_self, norm_zero] using hε))
    obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
    exact ⟨δ,hδ,fun t ht => hball (by simpa only [mem_ball, Real.dist_eq] using ht)⟩
  choose δ hδ hOsc using hδ
  obtain ⟨N,hN,tag,htags⟩ := compact_gauge_uniform_mesh
    (fun x => min (radius x) (δ x)) (fun x => lt_min (hr x) (hδ x))
  refine ⟨N,hN,tag,?_⟩
  intro i t ht
  have hh := htags i t ht
  exact ⟨hh.trans_le (min_le_left _ _),hOsc (tag i) t (hh.trans_le (min_le_right _ _))⟩

end Hindman168
