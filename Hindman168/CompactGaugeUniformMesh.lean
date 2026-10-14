import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A uniform finite mesh subordinate to an arbitrary positive local gauge
on [0,1]. Tags need not be cell endpoints. No uniform lower gauge bound is
assumed; compactness supplies a Lebesgue number before the mesh is chosen. -/
namespace Hindman168
open Set Metric

theorem compact_gauge_uniform_mesh (radius : Icc (0 : ℝ) 1 → ℝ)
    (hr : ∀ x, 0 < radius x) :
    ∃ N : ℕ, 0 < N ∧ ∃ tag : Fin N → Icc (0 : ℝ) 1,
      ∀ i : Fin N, ∀ x ∈ Icc ((i.val : ℝ)/N) (((i.val : ℝ)+1)/N),
        |x-(tag i : ℝ)| < radius (tag i) := by
  obtain ⟨δ,hδ,hcover⟩ := lebesgue_number_lemma_of_metric
    (s := Icc (0 : ℝ) 1) (c := fun x : Icc (0 : ℝ) 1 => ball (x : ℝ) (radius x))
    isCompact_Icc (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr ⟨x,hx⟩)⟩)
  obtain ⟨N,hN⟩ := exists_nat_gt (1/δ)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (one_div_pos.mpr hδ).trans hN
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hwidth : 1/(N : ℝ) < δ := by
    apply (div_lt_iff₀ hNR).mpr
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hleft (i : Fin N) : (i.val : ℝ)/N ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) hNR.le,?_⟩
    apply (div_le_one hNR).mpr
    exact_mod_cast i.isLt.le
  choose tag htag using fun i : Fin N => hcover ((i.val : ℝ)/N) (hleft i)
  refine ⟨N,hNpos,tag,?_⟩
  intro i x hx
  have hxball : x ∈ ball ((i.val : ℝ)/N) δ := by
    rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have he : (((i.val : ℝ)+1)/N)-(i.val : ℝ)/N = 1/(N : ℝ) := by ring
    linarith [hx.2]
  simpa only [mem_ball, Real.dist_eq] using htag i hxball

end Hindman168
