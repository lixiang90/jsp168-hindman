import Hindman168.ShortBinCutoffProbability

namespace Hindman168

open FiniteMass Filter
open scoped Topology Classical

def binaryDyadicCutoffGood (X p : ℕ) : Prop :=
  X ≤ 2 ^ Nat.log2 p ∧ 2 * 2 ^ Nat.log2 p ≤ X ^ 2

theorem binaryDyadic_cutoff_failure_band {X p : ℕ} (hX : 2 ≤ X)
    (hbad : ¬ binaryDyadicCutoffGood X p) :
    (p : ℝ) < 2 * X ∨ (X : ℝ) ^ 2 / 2 ≤ p := by
  by_cases hp : 0 < p
  · have hpl : 2 ^ Nat.log2 p ≤ p := Nat.log2_self_le hp.ne'
    have hpu : p < 2 * 2 ^ Nat.log2 p := by
      simpa only [pow_succ, mul_comm] using (Nat.lt_log2_self (n := p))
    by_cases hlo : X ≤ 2 ^ Nat.log2 p
    · have hhi : X ^ 2 < 2 * 2 ^ Nat.log2 p := by
        exact Nat.lt_of_not_ge (fun h => hbad ⟨hlo, h⟩)
      right
      have hh : X ^ 2 < 2 * p := hhi.trans_le (Nat.mul_le_mul_left 2 hpl)
      have hr : (X : ℝ) ^ 2 < 2 * p := by exact_mod_cast hh
      linarith
    · left
      have hh : p < 2 * X := hpu.trans (Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hlo) (by decide))
      exact_mod_cast hh
  · have hz : p = 0 := by omega
    left
    have hx : (2 : ℝ) ≤ X := by exact_mod_cast hX
    rw [hz, Nat.cast_zero]
    linarith

theorem rawMass_binaryDyadic_cutoff_bound {X W : ℕ}
    (hX : 2 ≤ X) (hW : 0 < W) (hlog : (W : ℝ) / X < Real.log X) :
    event (rawMass X W) (fun p => ¬ binaryDyadicCutoffGood X p) ≤
      2 * ((Real.log 2 + W / X) / (Real.log X - W / X)) := by
  have hn (p : ℕ) : 0 ≤ rawMass X W p := by
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (harmonicNormalizer_pos hX hW hlog) p
  exact (event_mono _ hn (fun _ hp => binaryDyadic_cutoff_failure_band hX hp)).trans
    (rawMass_cutoff_bands hX hW hlog (by norm_num) (by exact_mod_cast hX))

theorem rawMass_binaryDyadic_cutoff_tendsto {κ : Type*} {l : Filter κ}
    (X W : κ → ℕ) (hX : Tendsto (fun k => (X k : ℝ)) l atTop)
    (hWX : Tendsto (fun k => (W k : ℝ) / X k) l (𝓝 0))
    (hW : ∀ᶠ k in l, 0 < W k) :
    Tendsto (fun k => event (rawMass (X k) (W k))
      (fun p => ¬ binaryDyadicCutoffGood (X k) p)) l (𝓝 0) := by
  have hg : ∀ᶠ k in l, 2 ≤ X k ∧ 0 < W k ∧ (W k : ℝ) / X k < Real.log (X k) := by
    filter_upwards [hX.eventually (eventually_ge_atTop 2),
      (Real.tendsto_log_atTop.comp hX).eventually (eventually_ge_atTop 2),
      hWX.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hW] with k hx hl hw hp
    dsimp only [Function.comp_apply] at hl
    exact ⟨by exact_mod_cast hx, hp, by linarith⟩
  apply squeeze_zero' _ _ (harmonic_cutoff_band_bound_tendsto X W 2 hX hWX)
  · filter_upwards [hg] with k hk
    exact event_nonneg _ _ (fun p => by
      rw [rawMass_apply]
      exact harmonicWeight_nonneg (harmonicNormalizer_pos hk.1 hk.2.1 hk.2.2) p)
  · filter_upwards [hg] with k hk
    exact rawMass_binaryDyadic_cutoff_bound hk.1 hk.2.1 hk.2.2

end Hindman168
