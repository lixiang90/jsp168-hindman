import Hindman168.PolynomialRowDirectionCatalog
import Hindman168.OriginalDualTemplates

/-!
# Instantiating the actual master family and original dual from row data

The designated denominator is the product of the constructed responses.
The polynomial list and its nonzero proof are generated here, so master
construction and local-good normalization do not assume a list inclusion.
The row-minor hypotheses and block/gap data remain explicit obligations.
-/

namespace Hindman168.PolynomialRowFamily

open Filter
open scoped BigOperators Topology Classical
open Hindman168.FiniteMass

variable {n r m N K : ℕ}

noncomputable def catalogMaster
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (N : ℕ) (target : Fin r) :
    MasterParameterFamily :=
  constructedMasterFamily N (F.catalog target) (F.catalog_nonzero target)

theorem catalogMaster_conditions
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (N : ℕ) (target : Fin r)
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) :
    MasterParameterConditions N A (F.catalog target) (F.catalogMaster N target) :=
  constructedMasterFamily_conditions N A hA (F.catalog target) (F.catalog_nonzero target)

noncomputable def originalTemplate
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target : Fin r)
    (gap : ℕ → Fin N) (choice : ℕ → Fin K) : OriginalDualTemplate n N K where
  dimension := r - 1
  arity := n
  gap := gap
  choice := choice
  tests := F.catalog target
  denominator := F.denominator target
  denominator_mem := F.denominator_mem_catalog target
  masterSlot := id
  masterSlot_injective := Function.injective_id

theorem originalTemplate_conditions
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target : Fin r)
    (gap : ℕ → Fin N) (choice : ℕ → Fin K) (d : ℕ) (hr : 1 < r) (hd : r - 1 ≤ d)
    (tail : ℕ → Finset ℕ) (root : ℕ → Fin N)
    (htail : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val) :
    OriginalDualTemplateConditions (F.originalTemplate target gap choice)
      (F.catalog target) d tail root := by
  refine ⟨by dsimp [originalTemplate]; omega, hd, ?_, htail, hgap⟩
  intro f hf
  change f ∈ F.catalog target at hf
  change MvPolynomial.rename id f ∈ F.catalog target
  rw [MvPolynomial.rename_id_apply]
  exact hf

theorem local_good_responses_nonzero
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (target : Fin r)
    (master : MasterParameterFamily) (w : ℕ) (x : Fin n → ℕ)
    (hx : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    MvPolynomial.eval (fun k => (x k : ℤ)) (F.denominator target) ≠ 0 ∧
      (∀ l i, l ≠ i → MvPolynomial.eval (fun k => (x k : ℤ)) (F.response l i) ≠ 0) ∧
      ∀ i l, l ≠ i → ∃ k c,
        MvPolynomial.eval (fun k => (x k : ℤ))
          (polynomialRowMinor (F.row i) (F.row l) k c) ≠ 0 := by
  refine ⟨hx.1.2 _ (F.denominator_mem_catalog target), ?_, ?_⟩
  · intro l i hi
    exact hx.1.2 _ (F.response_mem_catalog target l i hi)
  · intro i l hl
    obtain ⟨k, c, hc⟩ := F.pair_minor i l hl
    exact ⟨k, c, hx.1.2 _ (F.minor_mem_catalog target i l k c hc)⟩

theorem catalog_local_good_event_tendsto_one
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (N : ℕ) (target : Fin r)
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) (gap : ℕ → Fin N) :
    Tendsto (fun w => event (primeIndependentMass n
      ((F.catalogMaster N target).pool w (gap w).val).lower
      ((F.catalogMaster N target).pool w (gap w).val).upper)
      (predictionLocalPrimeGoodEvent (F.catalogMaster N target)
        (F.catalog target) (F.denominator target) w)) atTop (𝓝 1) := by
  apply (F.catalogMaster_conditions N target A hA).local_prime_good_event_tendsto_one
    (F.catalog target) (F.denominator target) (F.denominator_mem_catalog target) id
    Function.injective_id _ gap
  intro f hf
  simpa only [MvPolynomial.rename_id_apply] using hf

theorem catalog_original_dense_models {b : ℕ}
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m) (N : ℕ) (target : Fin r)
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) (hr : 1 < r)
    (C : ℕ → Chain b) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin b) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (cut : ℝ) (hcut : predictionDualThreshold (r - 1) < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ ρ : ℤ → ℝ,
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ masterPredictionBlockMask (F.catalogMaster N target) C label w y) →
      ∃ model : ℤ → ℝ, (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
        ∀ u : OriginalSingleDualInput n (r - 1),
          u.Admissible (F.catalogMaster N target) C label w →
          |expectation (integerMass ((F.catalogMaster N target).cutoff w (root w).val) (primorial w))
            (fun y => (ρ y - model y) *
              (F.originalTemplate target gap choice).dual (F.catalogMaster N target) J u w y)| < η := by
  have hi : ∀ f ∈ F.catalog target, MvPolynomial.rename id f ∈ F.catalog target := by
    intro f hf
    simpa only [MvPolynomial.rename_id_apply] using hf
  exact (F.catalogMaster_conditions N target A hA).uniform_single_original_dense_models
    (F.catalog_nonzero target) (by omega) C hN label tail htail root gap htailroot htailgap
    hgap J hJ choice (F.catalog target) (F.denominator target) (F.denominator_mem_catalog target)
    id Function.injective_id hi cut hcut

end Hindman168.PolynomialRowFamily
