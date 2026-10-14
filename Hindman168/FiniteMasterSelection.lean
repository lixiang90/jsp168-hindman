import Hindman168.MasterSamplingBudgets

/-!
# Uniform growth when the selected master index varies

The master index set is finite and fixed before the asymptotic limit.
Finite choice therefore preserves every power-domination estimate.
Clamping the budget at each candidate index proves the result for an
arbitrary varying selected pivot, with only its actual budget constraint.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem PowerDominates.finite_choice {α ι : Type*} {l : Filter α} [Finite ι]
    {F Q : ι → α → ℝ} (h : ∀ i, PowerDominates l (F i) (Q i)) (index : α → ι) :
    PowerDominates l (fun w => F (index w) w) (fun w => Q (index w) w) := by
  intro n
  apply isLittleO_iff.mpr
  intro c hc
  have hall : ∀ᶠ w in l, ∀ i, ‖Q i w ^ n‖ ≤ c * ‖F i w‖ :=
    eventually_all.mpr (fun i => (h i n).bound hc)
  filter_upwards [hall] with w hw
  exact hw (index w)

theorem MasterParameterConditions.indexed_sampling_budget_growth {n N : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) {K H V : ℕ → ℕ}
    (hK : ∀ᶠ w in atTop, K w ≤ F.auxiliary w (index w).val)
    (hH : ∀ᶠ w in atTop, H w ≤ F.auxiliary w (index w).val)
    (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (index w).val : ℝ))
      (fun w => (samplingSize (primorial w) (K w) (H w) (V w) : ℝ)) := by
  have hi (i : Fin N) : PowerDominates atTop (fun w => Real.log (F.cutoff w i.val : ℝ))
      (fun w => (samplingSize (primorial w) (min (K w) (F.auxiliary w i.val))
        (min (H w) (F.auxiliary w i.val)) (min (V w) (F.auxiliary w i.val)) : ℝ)) :=
    hF.sampling_budget_growth i.val
      (Eventually.of_forall (fun _ => min_le_right _ _))
      (Eventually.of_forall (fun _ => min_le_right _ _))
      (Eventually.of_forall (fun _ => min_le_right _ _))
  apply (PowerDominates.finite_choice hi index).mono_base 1
  filter_upwards [hK, hH, hV] with w hKw hHw hVw
  simp only [pow_one, min_eq_left hKw, min_eq_left hHw, min_eq_left hVw]
  exact ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, le_rfl⟩

end Hindman168
