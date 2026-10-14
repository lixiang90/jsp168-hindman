import Hindman168.MaskSubsetReplacementPath

/-! The actual finite telescoping argument replacing all nonsingleton
factors. The bound is uniform over every remaining admissible factor and
product mask; no upper bound on intermediate counts is required. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open MaskOriginalSampling

theorem finite_difference_chain_abs_bound (x : ℕ → ℝ) (L : ℕ) (δ : ℝ)
    (h : ∀ k < L, |x k - x (k+1)| ≤ δ) : |x 0 - x L| ≤ (L : ℝ) * δ := by
  have bound : ∀ k ≤ L, |x 0 - x k| ≤ (k : ℝ) * δ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkL : k < L := by omega
      calc
        |x 0 - x (k+1)| = |(x 0 - x k) + (x k - x (k+1))| := by congr 1; ring
        _ ≤ |x 0 - x k| + |x k - x (k+1)| := abs_add_le _ _
        _ ≤ (k : ℝ) * δ + δ := add_le_add (ih (by omega)) (h k hkL)
        _ = ((k+1 : ℕ) : ℝ) * δ := by push_cast; ring
  exact bound L le_rfl

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
  (ρ model : Fin (m+1) → ℕ → ℤ → ℝ)
  (hm : ∀ col w y, 0 ≤ model col w y ∧ model col w y ≤ 1)
  (hρ : ∀ᶠ w in atTop, ∀ col y, 0 ≤ ρ col w y ∧
    ρ col w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
  (hcube : ∀ t : Fin (Fintype.card (LargeColumnSubset m)), Tendsto
    (fun w => maskEndpointTargetCube gap C t J w
      (fun y => ρ (targetRootAnchor gap t) w y - model (targetRootAnchor gap t) w y)) atTop (𝓝 0))

include ha hC hJ hgap htail hm hρ hcube in
theorem maskOriginalSubset_all_model_replacements_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b →
      (∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card → f U = ρ (U.val.max' U.property) w) →
      |maskOriginalSubsetCorrelation gap a C w f b -
        maskOriginalSubsetCorrelation gap a C w
          (maskSubsetModelReplacement f (fun col => model col w)) b| ≤ ε := by
  intro ε hε
  let L := Fintype.card (LargeColumnSubset m)
  let δ : ℝ := ε / ((L : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsteps (t : Fin (Fintype.card (LargeColumnSubset m))) :=
    maskOriginalSubset_single_model_replacement_uniform gap a C ha hC t J hJ hgap htail
      (ρ (targetRootAnchor gap t)) (model (targetRootAnchor gap t)) (hm _)
      (hρ.mono (fun w hw y => by simpa only [maskSourceTailMask_eq_targetBlock] using hw (targetRootAnchor gap t) y))
      (hcube t) δ hδ
  filter_upwards [eventually_all.mpr hsteps, maskSubsetTailMask_eventually_nonneg gap C hC] with w hw hν
  intro f b hf htarget
  have hchain (k : ℕ) (hk : k < L) :
      |maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid f (fun col => model col w) k) b -
        maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid f (fun col => model col w) (k+1)) b| ≤ δ := by
    let t : Fin (Fintype.card (LargeColumnSubset m)) := ⟨k, hk⟩
    have ht := htarget (maskSourceNonemptySupport m t) (maskSourceSupport_card m t)
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at ht
    have he := hw t (maskSubsetHybrid f (fun col => model col w) t.val) b
      (maskSubsetHybrid_admissible gap C w f b hf (fun col => model col w) (fun col y => hm col w y) hν t.val)
      ((maskSubsetHybrid_target_before f (fun col => model col w) t).trans ht)
    have hp := maskSubsetHybrid_step f (fun col => model col w) t
    rw [← maskTargetRootAnchor_eq_sourceMax gap t] at hp
    rw [← hp] at he
    exact he
  have he := finite_difference_chain_abs_bound
    (fun k => maskOriginalSubsetCorrelation gap a C w (maskSubsetHybrid f (fun col => model col w) k) b) L δ hchain
  dsimp only [L] at he
  simp only [maskSubsetHybrid_zero, maskSubsetHybrid_full] at he
  apply he.trans
  dsimp [δ]
  change (L : ℝ) * (ε / ((L : ℝ)+1)) ≤ ε
  rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (L : ℝ)+1)]
  nlinarith

include ha hC hJ hgap htail hm hρ hcube in
theorem maskOriginalSubset_all_model_replacements_tendsto_zero
    (f : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ᶠ w in atTop, maskOriginalSubsetAdmissible gap C w (f w) (b w))
    (htarget : ∀ᶠ w in atTop, ∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card →
      f w U = ρ (U.val.max' U.property) w) :
    Tendsto (fun w => maskOriginalSubsetCorrelation gap a C w (f w) (b w) -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetModelReplacement (f w) (fun col => model col w)) (b w))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [maskOriginalSubset_all_model_replacements_uniform gap a ha C hC J hJ hgap htail
      ρ model hm hρ hcube (ε/2) (by linarith), hf, htarget] with w hw hfw htw
    exact (hw (f w) (b w) hfw htw).trans_lt (by linarith)

end Hindman168
