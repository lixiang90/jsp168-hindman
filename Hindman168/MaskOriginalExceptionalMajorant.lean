import Hindman168.MaskBaseExceptionalDeletion
import Hindman168.MaskOriginalInsertionLimit
import Hindman168.FiniteRestrictedDomination

/-! The base-row catalogue majorant is reindexed to the actual original
source product. The entire bad-prime contribution vanishes uniformly over
all functions dominated on the original prime-pool support. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))
  (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))

noncomputable def originalMajorantProduct (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (z : Fin (m + 1) → ℤ) : ℝ :=
  ∏ base : MaskOriginalBaseRow m gap t, rowMajorant gap C t label w base
    ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm x
      (masterColumnCoefficient N a (fun w => (C w).block) w)
      (PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target base) z)

noncomputable def originalRowEnumeration (_w : ℕ)
    (u : Fin (Fintype.card (MaskOriginalBaseRow m gap t))) :
    Fin (maskGeneratedRowDataFamily m gap t).rowCount :=
  PolynomialRowFamily.additiveIndexEquiv (maskGeneratedRowDataFamily m gap t).target
    ((Fintype.equivFin (MaskOriginalBaseRow m gap t)).symm u)

noncomputable def originalLabelEnumeration (w : ℕ)
    (u : Fin (Fintype.card (MaskOriginalBaseRow m gap t))) : Fin (m + 1) :=
  label w ((Fintype.equivFin (MaskOriginalBaseRow m gap t)).symm u)

theorem originalRowEnumeration_injective (w : ℕ) :
    Function.Injective (originalRowEnumeration gap t w) :=
  (PolynomialRowFamily.additiveIndexEquiv _).injective.comp
    (Fintype.equivFin (MaskOriginalBaseRow m gap t)).symm.injective

theorem originalMajorantProduct_eq_enumerated (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) (z : Fin (m + 1) → ℤ) :
    originalMajorantProduct gap a C t label w x z =
      ∏ u, (1 + baseRowWeight gap a C t (originalLabelEnumeration gap t label)
        (originalRowEnumeration gap t) w u x z) := by
  exact (Fintype.prod_equiv (Fintype.equivFin (MaskOriginalBaseRow m gap t)).symm
    _ _ (fun _ => rfl)).symm

theorem originalRestrictedMajorant_eq_enumerated
    (E : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → Prop) (w : ℕ) :
    conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
      (E w) (originalMajorantProduct gap a C t label w) =
    baseRestrictedMajorant gap a C t (originalLabelEnumeration gap t label)
      (originalRowEnumeration gap t) E Finset.univ w := by
  unfold baseRestrictedMajorant conditionalFiniteAverage
  apply congrArg (expectation (basePrimeMass gap t w))
  funext x
  split_ifs
  · apply congrArg (expectation (maskOriginalBaseMass m gap C w))
    funext z
    exact originalMajorantProduct_eq_enumerated gap a C t label w x z
  · rfl

noncomputable def originalBadMajorantMass (w : ℕ) : ℝ :=
  conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
    (fun x => ¬ maskGeneratedCopiedPrimeGood m gap t w x)
    (originalMajorantProduct gap a C t label w)

include ha hC in
theorem originalBadMajorantMass_tendsto_zero
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    Tendsto (originalBadMajorantMass gap a C t label) atTop (𝓝 0) := by
  have ht := baseBadMajorant_tendsto_zero gap a ha C hC t hgap htail
    (originalLabelEnumeration gap t label) (originalRowEnumeration gap t)
    (Eventually.of_forall (originalRowEnumeration_injective gap t)) Finset.univ
  exact ht.congr (fun w => (originalRestrictedMajorant_eq_enumerated gap a C t label
    (fun w x => ¬ maskGeneratedCopiedPrimeGood m gap t w x) w).symm)

theorem originalProduct_majorant_bound
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hF : ∀ base y, |F w x base y| ≤ rowMajorant gap C t label w base y)
    (z : Fin (m + 1) → ℤ) :
    |originalProduct gap a C t F w x z| ≤ originalMajorantProduct gap a C t label w x z := by
  unfold originalProduct originalMajorantProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun base _ => hF base _)

include hC in
theorem original_bad_contribution_bound :
    ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
        (fun x => ¬ maskGeneratedCopiedPrimeGood m gap t w x)
        (originalProduct gap a C t (fun _ => F) w)| ≤ originalBadMajorantMass gap a C t label w := by
  filter_upwards [base_probability_eventually gap C hC] with w hb
  intro F hF
  apply conditionalFiniteAverage_abs_domination _ _ _ _ _ (basePrime_probability gap t w).1
    (fun _ _ _ => hb.1)
  intro x hx _ z _
  exact originalProduct_majorant_bound gap a C t label (fun _ => F) w x (hF x hx) z

include ha hC in
theorem original_bad_contribution_uniform_zero
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
    ∀ F : (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ,
      (∀ x ∈ (basePrimeMass gap t w).support, ∀ base y,
        |F x base y| ≤ rowMajorant gap C t label w base y) →
      |conditionalFiniteAverage (basePrimeMass gap t w) (fun _ => maskOriginalBaseMass m gap C w)
        (fun x => ¬ maskGeneratedCopiedPrimeGood m gap t w x)
        (originalProduct gap a C t (fun _ => F) w)| < ε := by
  intro ε hε
  filter_upwards [original_bad_contribution_bound gap a C hC t label,
    (originalBadMajorantMass_tendsto_zero gap a ha C hC t label hgap htail).eventually
      (eventually_lt_nhds hε)] with w hb he
  intro F hF
  exact (hb F hF).trans_lt he

end Hindman168.MaskOriginalSampling
