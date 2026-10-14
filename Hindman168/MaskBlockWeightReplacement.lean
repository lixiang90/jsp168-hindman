import Hindman168.MaskFiniteModelReplacementFamily

/-! Apply the constructed finite model family to the actual nonnegative
block weights themselves. Every original nonempty subset factor is sampled
at its actual normalized integer form; only nonsingletons are replaced.
The original product masks and singleton weights remain in the count. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))

noncomputable def maskBlockWeightFactors (ρ : Fin (m+1) → ℕ → ℤ → ℝ) (w : ℕ)
    (U : NonemptyColumnSubset (m+1)) : ℤ → ℝ := ρ (U.val.max' U.property) w

theorem maskBlockWeightFactors_admissible (w : ℕ) (ρ : Fin (m+1) → ℕ → ℤ → ℝ)
    (hρ : ∀ col y, 0 ≤ ρ col w y ∧
      ρ col w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (hb : ∀ V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅, ∀ y, |b V y| ≤ 1) :
    maskOriginalSubsetAdmissible gap C w (maskBlockWeightFactors ρ w) b := by
  refine ⟨?_, hb⟩
  intro U y
  change |ρ (U.val.max' U.property) w y| ≤ 1 + maskSubsetTailMask gap C w U y
  rw [abs_of_nonneg (hρ _ y).1, maskSubsetTailMask_eq_blockMask]
  exact (hρ _ y).2.trans (by linarith)

theorem maskGenerated_models_replace_blockWeights {ι : Type*} [Fintype ι]
    (d₀ : ℕ) (hd₀ : 0 < d₀) (coeff : ι → Fin (m+1) → ℚ) (hcoeff : ∀ i col, 0 < coeff i col)
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ : ι → Fin (m+1) → ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ i col y, 0 ≤ ρ i col w y ∧
      ρ i col w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (b : ι → ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hb : ∀ᶠ w in atTop, ∀ i V, V ∈ (Finset.univ : Finset (Fin (m+1))).powerset.erase ∅ →
      ∀ y, |b i w V y| ≤ 1)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ι → Fin (m+1) → ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ i col w y, 0 ≤ model i col w y ∧ model i col w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      (∀ i col, maskBlockModelDualControl gap C d₀ (ρ i col) (model i col) col) ∧
      (∀ᶠ w in atTop, ∀ i col, maskBlockModelDualPrefix gap C d₀ (stage w) (ρ i col) (model i col) col w) ∧
      ∀ i, Tendsto (fun w =>
        maskOriginalSubsetCorrelation gap (coeff i) C w (maskBlockWeightFactors (ρ i) w) (b i w) -
        maskOriginalSubsetCorrelation gap (coeff i) C w
          (maskSubsetModelReplacement (maskBlockWeightFactors (ρ i) w) (fun col => model i col w)) (b i w))
        atTop (𝓝 0) := by
  obtain ⟨stage, model, hs, hsw, hm, hPw, hdual, _, hquality, hprefix, _⟩ :=
    maskGenerated_finite_model_replacement_family gap C d₀ hd₀ coeff hcoeff hC hgap htail ρ hρ P hP
  refine ⟨stage, model, hs, hsw, hm, hPw, hdual, hprefix, ?_⟩
  intro i
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [hquality (ε/2) (by linarith), hρ, hb] with w hw hr hbw
    have hf := maskBlockWeightFactors_admissible gap C w (ρ i) (hr i) (b i w) (hbw i)
    exact (hw i _ (b i w) hf (fun _ _ => rfl)).trans_lt (by linarith)

end Hindman168
