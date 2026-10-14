import Hindman168.MaskBlockModelChainCorrelations
import Hindman168.MasterColumnCoefficients

/-! Actual color weights use the paper's original master block coefficient.
They are zero on nonpositive integers, partition the positive color inputs,
and admit one bounded model controlling all block gaps and quotient scales.
The rational scaling is eventually exactly the positive integer coefficient. -/

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def maskBlockColorIndicator {r : ℕ} (N : ℕ) (T : Finset ℕ) (i : ℕ)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) (w : ℕ) (y : ℤ) : ℝ :=
  if 0 < y then
    if χ (masterColumnCoefficient N (fun _ : Fin 1 => a)
      (fun _ _ => insert i T) w 0 * y.toNat) = c then 1 else 0
  else 0

noncomputable def maskBlockColorWeight {r N : ℕ} (m : ℕ) (hN : 0 < N)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) (w : ℕ) (y : ℤ) : ℝ :=
  masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
    (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y *
      maskBlockColorIndicator N T i.val a χ c w y

theorem maskBlockColorIndicator_unit {r : ℕ} (N : ℕ) (T : Finset ℕ) (i : ℕ)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) (w : ℕ) (y : ℤ) :
    0 ≤ maskBlockColorIndicator N T i a χ c w y ∧
      maskBlockColorIndicator N T i a χ c w y ≤ 1 := by
  unfold maskBlockColorIndicator
  split_ifs <;> norm_num

theorem maskBlockColorIndicator_sum {r : ℕ} (N : ℕ) (T : Finset ℕ) (i : ℕ)
    (a : ℚ) (χ : ℕ → Fin r) (w : ℕ) (y : ℤ) :
    ∑ c : Fin r, maskBlockColorIndicator N T i a χ c w y = if 0 < y then 1 else 0 := by
  by_cases hy : 0 < y
  · simp [maskBlockColorIndicator, hy]
  · simp [maskBlockColorIndicator, hy]

theorem maskBlockColorWeight_bounds {r N : ℕ} (m : ℕ) (hN : 0 < N)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (c : Fin r) :
    ∀ᶠ w in atTop, ∀ y, 0 ≤ maskBlockColorWeight m hN T i hT hTi a χ c w y ∧
      maskBlockColorWeight m hN T i hT hTi a χ c w y ≤
        masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
          (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y := by
  have hν := (maskGeneratedMaster_conditions m (fun _ => ⟨0, hN⟩) ∅ (by simp)).block_mask_eventually_nonneg
    (fun _ => maskBlockChain T i.val hT hTi)
      (fun _ => maskBlockChain_block_range T i hT hTi) (fun _ => 0)
  filter_upwards [hν] with w hw
  intro y
  have hf := maskBlockColorIndicator_unit N T i.val a χ c w y
  exact ⟨mul_nonneg (hw y) hf.1, (mul_le_mul_of_nonneg_left hf.2 (hw y)).trans_eq (mul_one _)⟩

theorem maskBlockColorWeight_sum {r N : ℕ} (m : ℕ) (hN : 0 < N)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (χ : ℕ → Fin r) (w : ℕ) (y : ℤ) :
    ∑ c : Fin r, maskBlockColorWeight m hN T i hT hTi a χ c w y =
      masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y *
        (if 0 < y then 1 else 0) := by
  simp only [maskBlockColorWeight, ← Finset.mul_sum, maskBlockColorIndicator_sum]

theorem maskBlockColorCoefficient_exact {N : ℕ} (m : ℕ) (hN : 0 < N)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (a : ℚ) (ha : 0 < a) :
    ∀ᶠ w in atTop,
      0 < masterColumnCoefficient N (fun _ : Fin 1 => a) (fun _ _ => insert i.val T) w 0 ∧
      (masterScale (primorial w) w N (insert i.val T) : ℚ) * a =
        (masterColumnCoefficient N (fun _ : Fin 1 => a) (fun _ _ => insert i.val T) w 0 : ℚ) := by
  have h := (maskGeneratedMaster_conditions m (fun _ => ⟨0, hN⟩) {a} (by simpa using ha)).column_coefficients
    (fun _ : Fin 1 => a) (fun _ => by simp)
      (fun _ _ => insert i.val T) (fun _ col => maskBlockChain_block_range T i hT hTi col)
      (fun _ _ => Finset.insert_nonempty _ _)
  exact h.mono (fun _ hw => ⟨(hw 0).1, (hw 0).2.1⟩)

theorem maskBlock_coloring_all_gap_dense_models {r N : ℕ} (m d₀ : ℕ) (hd₀ : 0 < d₀)
    (hN : 0 < N) (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty)
    (hTi : T ⊆ Finset.range i.val) (a : ℚ) (ha : 0 < a)
    (χ : ℕ → Fin r) (c : Fin r) :
    ∃ model : ℕ → ℤ → ℝ, (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      ∀ l : MaskValidBlockGap T i,
        ∀ t : Fin (Fintype.card (LargeColumnSubset m) + 1),
        ∀ J : ℕ, 1 ≤ J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).arity
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dimension,
        u.Admissible (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
          (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w →
        |expectation (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val)
          (primorial w)) (fun y =>
            (maskBlockColorWeight m hN T i hT hTi a χ c w y - model w y) *
            (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dual
              (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) (fun _ => J) u w y)| < η := by
  obtain ⟨_, model, _, _, hm, _, hd⟩ := maskBlock_all_gap_dense_models m d₀ hd₀ hN {a}
    (by simpa using ha) T i hT hTi (maskBlockColorWeight m hN T i hT hTi a χ c)
    (maskBlockColorWeight_bounds m hN T i hT hTi a χ c)
    (fun _ _ => True) (fun _ => Eventually.of_forall (fun _ => True.intro))
  exact ⟨model, hm, hd⟩

end Hindman168
