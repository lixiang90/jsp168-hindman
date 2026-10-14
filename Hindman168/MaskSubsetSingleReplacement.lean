import Hindman168.MaskSubsetReplacementData
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact single-factor replacement in the original subset count, followed
by the actual model-error detection estimate. The original root weights,
all other subset factors and all product masks are retained. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))

theorem maskSubsetProduct_update (f : NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (U : NonemptyColumnSubset (m+1)) (g : ℤ → ℝ)
    (L : NonemptyColumnSubset (m+1) → ℤ) :
    (∏ V : NonemptyColumnSubset (m+1), Function.update f U g V (L V)) =
      g (L U) * ∏ V ∈ (Finset.univ : Finset (NonemptyColumnSubset (m+1))).erase U, f V (L V) := by
  have he : (fun V => Function.update f U g V (L V)) =
      Function.update (fun V => f V (L V)) U (g (L U)) := by
    funext V
    by_cases h : V = U
    · subst V; simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  rw [he, Finset.prod_update_of_mem (Finset.mem_univ U), Finset.sdiff_singleton_eq_erase]

theorem maskOriginalSubsetCorrelation_update_difference (w : ℕ)
    (f : NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : Finset (Fin (m+1)) → ℤ → ℝ)
    (U : NonemptyColumnSubset (m+1)) (g : ℤ → ℝ) :
    maskOriginalSubsetCorrelation gap a C w f b -
      maskOriginalSubsetCorrelation gap a C w (Function.update f U g) b =
    maskOriginalSubsetCorrelation gap a C w (Function.update f U (fun y => f U y - g y)) b := by
  unfold maskOriginalSubsetCorrelation
  rw [← expectation_sub]
  apply congrArg (expectation (maskOriginalBaseMass m gap C w))
  funext z
  rw [maskSubsetProduct_update, maskSubsetProduct_update]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (NonemptyColumnSubset (m+1)))
    (fun V => f V (maskSubsetIntegerForm (masterColumnCoefficient N a (fun w => (C w).block) w) V z))
    (Finset.mem_univ U)]
  ring

theorem maskOriginalSubset_single_model_replacement_uniform (ha : ∀ col, 0 < a col)
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ maskSubsetTailMask gap C w (maskSourceNonemptySupport m t) y)
    (hcube : Tendsto (fun w => maskEndpointTargetCube gap C t J w
      (fun y => ρ w y - model w y)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b →
      f (maskSourceNonemptySupport m t) = ρ w →
      |maskOriginalSubsetCorrelation gap a C w f b -
        maskOriginalSubsetCorrelation gap a C w
          (Function.update f (maskSourceNonemptySupport m t) (model w)) b| ≤ ε := by
  intro ε hε
  filter_upwards [hρ, maskTargetError_original_detection_uniform gap a ha C hC t J hJ hgap htail
    (fun w y => ρ w y - model w y) hcube hε] with w hr hw
  intro f b hf htarget
  have he := maskOriginalSubset_update_admissible gap C w f b hf (maskSourceNonemptySupport m t)
    (fun y => ρ w y - model w y) (fun y => model_error_abs_bound (hr y) (hm w y))
  rw [maskOriginalSubsetCorrelation_update_difference, htarget]
  exact hw _ b he (by simp only [Function.update_self])

end Hindman168
