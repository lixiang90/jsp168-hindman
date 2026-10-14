import Hindman168.FiniteMasterSelection

/-!
# Product-modulus sampling budgets

A fixed number q of divisors bounded by V has product at most V^q.
Domination of all powers of the original budget therefore supplies
domination of all powers of the product-modulus budget. The latter
does not need to be smaller than the selected master auxiliary value.
-/

namespace Hindman168

open Filter Asymptotics
open scoped Topology

theorem samplingSize_power_cap (W V q : ℕ) :
    samplingSize W (V ^ q) 0 V ≤ (samplingSize W V 0 V) ^ (q + 3) := by
  let S := samplingSize W V 0 V
  have hb := samplingSize_bounds W V 0 V
  have htwo : 2 ≤ S := hb.1
  have hone : 1 ≤ S := by omega
  have hW : W ≤ S := hb.2.1
  have hV : V ≤ S := hb.2.2.1
  have hS : S ≤ S ^ (q + 1) := by
    calc
      S = S ^ 1 := by simp
      _ ≤ S ^ (q + 1) := pow_le_pow_right₀ hone (by omega)
  have hVp : V ^ q ≤ S ^ (q + 1) :=
    (Nat.pow_le_pow_left hV q).trans (pow_le_pow_right₀ hone (by omega))
  have hfour : 4 ≤ S ^ 2 := by nlinarith
  calc
    samplingSize W (V ^ q) 0 V ≤ 4 * S ^ (q + 1) := by
      unfold samplingSize
      omega
    _ ≤ S ^ 2 * S ^ (q + 1) := Nat.mul_le_mul_right _ hfour
    _ = S ^ (q + 3) := by rw [← pow_add]; congr 1; omega

theorem PowerDominates.sampling_power_cap {α : Type*} {l : Filter α}
    {F : α → ℝ} {W V : α → ℕ}
    (h : PowerDominates l F (fun w => (samplingSize (W w) (V w) 0 (V w) : ℝ)))
    (q : ℕ) :
    PowerDominates l F (fun w => (samplingSize (W w) (V w ^ q) 0 (V w) : ℝ)) := by
  apply h.mono_base (q + 3)
  apply Eventually.of_forall
  intro w
  refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_⟩
  exact_mod_cast samplingSize_power_cap (W w) (V w) q

theorem MasterParameterConditions.indexed_product_sampling_growth {n N : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (index : ℕ → Fin N) (q : ℕ)
    {V : ℕ → ℕ} (hV : ∀ᶠ w in atTop, V w ≤ F.auxiliary w (index w).val) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (index w).val : ℝ))
      (fun w => (samplingSize (primorial w) (V w ^ q) 0 (V w) : ℝ)) :=
  (hF.indexed_sampling_budget_growth index hV
    (Eventually.of_forall (fun _ => Nat.zero_le _)) hV).sampling_power_cap q

end Hindman168
