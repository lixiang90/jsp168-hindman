import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-! The epsilon/eventual formulation implies the actual length-first local limsup.
No diagonal sequence of locality parameters is substituted for the iterated limit. -/
namespace Hindman168
open Filter Set
open scoped Topology

theorem nonnegative_iterated_local_limsup (a : ℝ → ℕ → ℝ)
    (ha : ∀ α m, 0 ≤ a α m)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ α0 : ℝ, 0 < α0 ∧
      ∀ α : ℝ, 0 < α → α < α0 → ∀ᶠ m in atTop, a α m < ε) :
    Tendsto (fun α => limsup (a α) atTop) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,he⟩ := hlocal (ε/2) (by positivity)
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨r,hr,?_⟩
  intro α hα
  have hupper : ∀ᶠ m in atTop, a α m ≤ ε/2 := (he α hα.1 hα.2).mono (fun _ h => h.le)
  have hbound : atTop.IsBoundedUnder (· ≤ ·) (a α) := ⟨ε/2,hupper⟩
  have hnonneg : 0 ≤ limsup (a α) atTop := by
    apply le_limsup_of_le hbound
    intro b hb
    obtain ⟨m,hm⟩ := hb.exists
    exact (ha α m).trans hm
  have hup : limsup (a α) atTop ≤ ε/2 :=
    limsup_le_of_le (isCoboundedUnder_le_of_le atTop (ha α)) hupper
  change dist (limsup (a α) atTop) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  linarith

end Hindman168
