import Hindman168.PositivePrincipalSumPivotMasterBoundary

namespace Hindman168
open Filter FiniteMass
open scoped Topology BigOperators Classical

/-- Original-master version of (8.28), uniform in EVERY earlier event.
Only the local shifted success coverage and unconditional bad-conditioning
limit remain inputs from the geometric extraction. The error sequence may
depend on the fixed models; the multiplier c/card(V) does not. -/
theorem principal_master_pivot_extension
    {d N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (i : Fin N) {α V : Type*} [Fintype V] [Nonempty V]
    (μ : ℕ → Mass α) (G : ℕ → α → Prop) (P : ℕ → α → ℤ → Prop)
    (s : V → ℕ → α → ℤ) (C c : ℝ) (p : ℕ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hμ : ∀ᶠ w in atTop, (∀ x, 0 ≤ μ w x) ∧ total (μ w) = 1)
    (hbad : Tendsto (fun w => event (μ w) (fun x => ¬ G w x)) atTop (𝓝 0))
    (hs : ∀ᶠ w in atTop, ∀ v x, x ∈ (μ w).support →
      (primorial w : ℤ) ∣ s v w x ∧ |(s v w x : ℝ)| ≤ C * (F.auxiliary w i.val : ℝ)^p)
    (hgood : ∀ᶠ w in atTop, ∀ x ∈ (μ w).support, G w x →
      c ≤ ∑ v, event (integerMass (F.cutoff w i.val) (primorial w))
        (fun z => P w x (z + s v w x))) :
    ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ᶠ w in atTop, ∀ E : α → Prop,
      (c / Fintype.card V) * event (μ w) E - err w ≤
        event (conditionalJoint (μ w) (fun _ => integerMass (F.cutoff w i.val) (primorial w)))
          (fun xp => E xp.1 ∧ P w xp.1 xp.2) := by
  let b w := 2 * (C * (F.auxiliary w i.val : ℝ)^p) /
    ((F.cutoff w i.val : ℝ) * (Real.log (F.cutoff w i.val : ℝ) -
      (primorial w : ℝ) / F.cutoff w i.val))
  let err w := (c / Fintype.card V) * event (μ w) (fun x => ¬ G w x) + b w
  refine ⟨err, ?_, ?_⟩
  · have hb := principal_master_harmonic_boundary_tendsto hF i.val p C hC
    simpa [err, b] using (hbad.const_mul (c / Fintype.card V)).add hb
  · filter_upwards [hμ, hs, hgood, hF.raw_cutoffs_valid] with w hm hsw hg hv E
    have hvw := hv i.val (Finset.mem_range.mpr i.isLt)
    have h := principal_harmonic_pivot_extension (μ w) E (G w) (P w)
      (F.cutoff w i.val) (primorial w) (fun v => s v w)
      (C * (F.auxiliary w i.val : ℝ)^p) c hm.1 hvw.1 (primorial_pos w) hvw.2.1
      (mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) _)) hc hsw hg
    rw [hm.2, mul_one] at h
    change _ - (_ + b w) ≤ _
    change _ - _ - b w ≤ _ at h
    linarith
end Hindman168
