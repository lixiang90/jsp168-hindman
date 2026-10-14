import Hindman168.ShortBinCutoffGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.Order.Field

/-! The whole short-bin preimage discard has vanishing original harmonic
probability. The event permits any bin and any tail product in the common
range, so it covers bins chosen from the actual product sample. -/

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

def failedCutoffShortBin (X R tlo C : ℝ) (p : ℕ) : Prop :=
  ∃ Q t, tlo ≤ t ∧ t ≤ C * tlo ∧ Q ≤ t * p ∧ t * p < Q + tlo * R ∧
    ∃ t', tlo ≤ t' ∧ t' ≤ C * tlo ∧
      (Q / t' < X + 2 * R ∨ X ^ 2 - 2 * R < (Q + tlo * R) / t')

theorem rawMass_failedCutoffShortBin_bound {X W : ℕ} {R tlo C : ℝ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X)
    (htlo : 0 < tlo) (hC : 1 ≤ C) (hCX : 2 * C ≤ X)
    (hR : 0 ≤ R) (hsmall : 6 * R ≤ X) :
    event (rawMass X W) (failedCutoffShortBin X R tlo C) ≤
      2 * ((Real.log (2 * C) + W / X) / (Real.log X - W / X)) := by
  have hn (p : ℕ) : 0 ≤ rawMass X W p := by
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (harmonicNormalizer_pos hX hW hlog) p
  apply (event_mono (rawMass X W) hn ?_).trans
    (rawMass_cutoff_bands hX hW hlog (by linarith : 1 < 2 * C) hCX)
  intro p hp
  obtain ⟨Q, t, ht, htC, hbinLo, hbinHi, hbad⟩ := hp
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  exact shortBin_failed_cutoff_pivot_band htlo hC hx hR hsmall ht htC
    (Nat.cast_nonneg p) hbinLo hbinHi hbad

theorem harmonic_cutoff_band_bound_tendsto {κ : Type*} {l : Filter κ}
    (X W : κ → ℕ) (C : ℝ)
    (hX : Tendsto (fun k => (X k : ℝ)) l atTop)
    (hWX : Tendsto (fun k => (W k : ℝ) / X k) l (𝓝 0)) :
    Tendsto (fun k => 2 * ((Real.log C + (W k : ℝ) / X k) /
      (Real.log (X k) - (W k : ℝ) / X k))) l (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp hX
  have hd : Tendsto (fun k => Real.log (X k) - (W k : ℝ) / X k) l atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop (b + 1)),
      hWX.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk hw
    dsimp only [Function.comp_apply] at hk
    linarith
  have hn : Tendsto (fun k => Real.log C + (W k : ℝ) / X k) l (𝓝 (Real.log C)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hWX
  simpa only [mul_zero] using (hn.div_atTop hd).const_mul 2

theorem rawMass_failedCutoffShortBin_tendsto {κ : Type*} {l : Filter κ}
    (X W : κ → ℕ) (R tlo : κ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hX : Tendsto (fun k => (X k : ℝ)) l atTop)
    (hWX : Tendsto (fun k => (W k : ℝ) / X k) l (𝓝 0))
    (hRX : Tendsto (fun k => R k / X k) l (𝓝 0))
    (hW : ∀ᶠ k in l, 0 < W k) (hR : ∀ᶠ k in l, 0 ≤ R k)
    (htlo : ∀ᶠ k in l, 0 < tlo k) :
    Tendsto (fun k => event (rawMass (X k) (W k))
      (failedCutoffShortBin (X k) (R k) (tlo k) C)) l (𝓝 0) := by
  have hg : ∀ᶠ k in l, 2 ≤ X k ∧ 0 < W k ∧
      (W k : ℝ) / X k < Real.log (X k) ∧ 0 < tlo k ∧
      2 * C ≤ X k ∧ 0 ≤ R k ∧ 6 * R k ≤ X k := by
    filter_upwards [hX.eventually (eventually_ge_atTop (2 * C)),
      (Real.tendsto_log_atTop.comp hX).eventually (eventually_ge_atTop 2),
      hWX.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hRX.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6)), hW, hR, htlo]
      with k hx hl hw hr hwpos hrpos htpos
    dsimp only [Function.comp_apply] at hl
    have hx2R : (2 : ℝ) ≤ X k := by linarith
    have hx2 : 2 ≤ X k := by exact_mod_cast hx2R
    have hxp : (0 : ℝ) < X k := by linarith
    have hmul := (div_lt_iff₀ hxp).mp hr
    exact ⟨hx2, hwpos, by linarith, htpos, hx, hrpos, by linarith⟩
  apply squeeze_zero' (hg.mono (fun k hk => event_nonneg _ _ (fun p => by
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (harmonicNormalizer_pos hk.1 hk.2.1 hk.2.2.1) p)))
    (hg.mono (fun k hk => rawMass_failedCutoffShortBin_bound hk.1 hk.2.1 hk.2.2.1
      hk.2.2.2.1 hC hk.2.2.2.2.1 hk.2.2.2.2.2.1 hk.2.2.2.2.2.2))
    (harmonic_cutoff_band_bound_tendsto X W (2 * C) hX hWX)

end Hindman168
