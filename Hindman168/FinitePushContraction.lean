import Hindman168.FiniteMixture
import Hindman168.JointSamplingAsymptotics

/-! Coefficient L1 contraction and finite choices of rapid errors. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem variation_single {α : Type*} (a : α) (r : ℝ) :
    variation (Finsupp.single a r) = |r| := by
  simp [variation]

theorem variation_push_le {α β : Type*} (μ : Mass α) (f : α → β) :
    variation (μ.mapDomain f) ≤ variation μ := by
  rw [Finsupp.mapDomain, Finsupp.sum]
  exact (variation_finset_sum μ.support (fun a => Finsupp.single (f a) (μ a))).trans_eq
    (by simp only [variation_single]; rfl)

theorem distance_push_le {α β : Type*} (μ ν : Mass α) (f : α → β) :
    distance (μ.mapDomain f) (ν.mapDomain f) ≤ distance μ ν := by
  rw [distance, ← Finsupp.mapDomain_sub]
  exact variation_push_le (μ - ν) f

end Hindman168.FiniteMass

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem RapidlySmall.finite_choice {α ι : Type*} {l : Filter α} [Finite ι]
    {U e : ι → α → ℝ} (he : ∀ i, RapidlySmall l (U i) (e i))
    (index : α → ι) {V : α → ℝ} (hV : ∀ᶠ w in l, 0 < V w)
    (hVU : ∀ᶠ w in l, V w ≤ U (index w) w) :
    RapidlySmall l V (fun w => e (index w) w) := by
  intro C
  apply isLittleO_iff.mpr
  intro c hc
  have hall := eventually_all.mpr (fun i => (he i C).bound hc)
  filter_upwards [hall, hV, hVU] with w hw hVw hVUw
  have hU : 0 < U (index w) w := hVw.trans_le hVUw
  have hh := hw (index w)
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hU C))] at hh
  simp only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hVw C))]
  exact hh.trans (mul_le_mul_of_nonneg_left
    (inv_le_inv₀ (pow_pos hU C) (pow_pos hVw C) |>.mpr
      (pow_le_pow_left₀ hVw.le hVUw C)) hc.le)

end Hindman168
