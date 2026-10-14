import Hindman168.PositivePrincipalSumPivotPaths
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Hindman168
open Filter
open scoped Topology BigOperators

/-- The deterministic lower budget retains every finite error before taking
limits. No error rate uniform in the subsequently chosen model is needed. -/
noncomputable def principalPivotLowerBudget {K : Type*}
    (c : ℕ → ℝ) (err : ℕ → K → ℝ) : ℕ → K → ℝ
  | 0, _ => 1
  | i+1, w => c i * principalPivotLowerBudget c err i w - err i w

theorem principal_pivot_lower_budget_le {K : Type*} (L : Filter K)
    (c : ℕ → ℝ) (err p : ℕ → K → ℝ) (n : ℕ)
    (hc : ∀ i < n, 0 ≤ c i)
    (hzero : ∀ᶠ w in L, 1 ≤ p 0 w)
    (hstep : ∀ i < n, ∀ᶠ w in L, c i * p i w - err i w ≤ p (i+1) w) :
    ∀ᶠ w in L, principalPivotLowerBudget c err n w ≤ p n w := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    filter_upwards [ih (fun i hi => hc i (by omega))
      (fun i hi => hstep i (by omega)), hstep n (by omega)] with w hw hs
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hw (hc n (by omega))) _).trans hs

theorem principal_pivot_lower_budget_tendsto {K : Type*} (L : Filter K)
    (c : ℕ → ℝ) (err : ℕ → K → ℝ) (n : ℕ)
    (herr : ∀ i < n, Tendsto (err i) L (𝓝 0)) :
    Tendsto (principalPivotLowerBudget c err n) L (𝓝 (∏ i ∈ Finset.range n, c i)) := by
  induction n with
  | zero => simpa [principalPivotLowerBudget] using (tendsto_const_nhds (x := (1 : ℝ)))
  | succ n ih =>
    have h := ((ih (fun i hi => herr i (by omega))).const_mul (c n)).sub (herr n (by omega))
    simpa [principalPivotLowerBudget, Finset.prod_range_succ, mul_comm] using h

/-- The finite-pivot product survives arbitrary model-dependent vanishing
errors. Bounds [0,1] are only used to define the ordinary real liminf. -/
theorem principal_finite_pivot_liminf {K : Type*} (L : Filter K) [L.NeBot]
    (c : ℕ → ℝ) (err p : ℕ → K → ℝ) (n : ℕ)
    (hc : ∀ i < n, 0 ≤ c i)
    (hzero : ∀ᶠ w in L, 1 ≤ p 0 w)
    (hstep : ∀ i < n, ∀ᶠ w in L, c i * p i w - err i w ≤ p (i+1) w)
    (herr : ∀ i < n, Tendsto (err i) L (𝓝 0))
    (hp : ∀ᶠ w in L, p n w ∈ Set.Icc (0 : ℝ) 1) :
    (∏ i ∈ Finset.range n, c i) ≤ L.liminf (p n) := by
  have ht := principal_pivot_lower_budget_tendsto L c err n herr
  have hlo := principal_pivot_lower_budget_le L c err p n hc hzero hstep
  have hu : L.IsBoundedUnder (· ≥ ·) (p n) := ⟨0, hp.mono (fun _ h => h.1)⟩
  have hv : L.IsCoboundedUnder (· ≥ ·) (p n) :=
    (show L.IsBoundedUnder (· ≤ ·) (p n) from ⟨1, hp.mono (fun _ h => h.2)⟩).isCoboundedUnder_ge
  apply (le_liminf_iff hv hu).mpr
  intro a ha
  filter_upwards [ht.eventually (Ioi_mem_nhds ha), hlo] with w hw hl
  exact hw.trans_le hl

/-- Actual finite-mass path induction. Each level's successful events are
partitioned afresh; only the explicit individual path bounds are inputs. -/
theorem principal_finite_path_mass_liminf {K α I : Type*} [Fintype I]
    (L : Filter K) [L.NeBot] (μ : K → FiniteMass.Mass α)
    (E R : ℕ → I → K → α → Prop) (c : ℕ → ℝ) (err : ℕ → I → K → ℝ) (n : ℕ)
    (hμ : ∀ᶠ w in L, (∀ x, 0 ≤ μ w x) ∧ FiniteMass.total (μ w) = 1)
    (hc : ∀ i < n, 0 ≤ c i)
    (hzero : ∀ᶠ w in L, ∀ x, ∃ j, E 0 j w x)
    (hdis : ∀ i < n, ∀ᶠ w in L, ∀ x j k, E i j w x → E i k w x → j = k)
    (hsub : ∀ i < n, ∀ᶠ w in L, ∀ j x, R i j w x → E i j w x)
    (hnext : ∀ i < n, ∀ᶠ w in L, ∀ x, (∃ j, R i j w x) ↔ ∃ j, E (i+1) j w x)
    (hstep : ∀ i < n, ∀ᶠ w in L, ∀ j,
      c i * FiniteMass.event (μ w) (E i j w) - err i j w ≤
        FiniteMass.event (μ w) (R i j w))
    (herr : ∀ i < n, ∀ j, Tendsto (err i j) L (𝓝 0)) :
    (∏ i ∈ Finset.range n, c i) ≤
      L.liminf (fun w => FiniteMass.event (μ w) (fun x => ∃ j, E n j w x)) := by
  apply principal_finite_pivot_liminf L c (fun i w => ∑ j, err i j w)
    (fun i w => FiniteMass.event (μ w) (fun x => ∃ j, E i j w x)) n hc
  · filter_upwards [hμ, hzero] with w hm hz
    have he : (fun x => ∃ j, E 0 j w x) = (fun _ => True) :=
      funext (fun x => propext ⟨fun _ => trivial, fun _ => hz x⟩)
    rw [he]
    simpa [FiniteMass.event, FiniteMass.total] using hm.2.ge
  · intro i hi
    filter_upwards [hdis i hi, hsub i hi, hnext i hi, hstep i hi] with w hd hs hn ht
    have h := principal_path_extension_sum (μ w) (fun j => E i j w) (fun j => R i j w)
      hd hs (c i) (fun j => err i j w) ht
    convert h using 1
    congr 1
    exact funext (fun x => propext (hn x).symm)
  · intro i hi
    simpa using tendsto_finsetSum Finset.univ (fun j _ => herr i hi j)
  · filter_upwards [hμ] with w hm
    exact ⟨FiniteMass.event_nonneg _ _ hm.1, (FiniteMass.event_le_total _ _ hm.1).trans_eq hm.2⟩

/-- Chosen solely from the finite plan catalogues, before thresholds/models.
Inactive pivots can be omitted; the empty product is exactly one. -/
noncomputable def principalPivotDelta (Q V : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, 1 / (3 * (Q i : ℝ) * (V i : ℝ))

theorem principal_pivot_delta_pos (Q V : ℕ → ℕ) (n : ℕ)
    (hQ : ∀ i < n, 0 < Q i) (hV : ∀ i < n, 0 < V i) :
    0 < principalPivotDelta Q V n := by
  apply Finset.prod_pos
  intro i hi
  have hq : (0 : ℝ) < Q i := Nat.cast_pos.mpr (hQ i (Finset.mem_range.mp hi))
  have hv : (0 : ℝ) < V i := Nat.cast_pos.mpr (hV i (Finset.mem_range.mp hi))
  positivity
end Hindman168
