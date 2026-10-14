import Hindman168.PolynomialRowCatalogApplication
import Hindman168.OriginalZeroPrimeTemplate
import Hindman168.MasterCountableOriginalDenseModels

/-!
# One actual master list for heterogeneous polynomial-row cube types

Each row type has its own local prime arity, row/column counts, denominator,
gap and injective slots. Renamed generated catalogues form a fixed finite
master list, augmented by 1 for the extra zero-prime type. The derived list
and actual master construction supply one bounded model sequence for every
fixed positive quotient scale. Mask-generated row evidence, block data and
companion diagonal requirements are not inferred here.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

structure OriginalPolynomialRowData (n N : ℕ) where
  arity : ℕ
  rowCount : ℕ
  offColumns : ℕ
  rows : PolynomialRowFamily (MvPolynomial (Fin arity) ℤ) rowCount offColumns
  rowCount_gt_one : 1 < rowCount
  target : Fin rowCount
  slot : Fin arity → Fin n
  slot_injective : Function.Injective slot
  gap : ℕ → Fin N

noncomputable def OriginalPolynomialRowData.template {n N : ℕ}
    (T : OriginalPolynomialRowData n N) : OriginalDualTemplate n N 1 where
  dimension := T.rowCount - 1
  arity := T.arity
  gap := T.gap
  choice := fun _ => 0
  tests := T.rows.catalog T.target
  denominator := T.rows.denominator T.target
  denominator_mem := T.rows.denominator_mem_catalog T.target
  masterSlot := T.slot
  masterSlot_injective := T.slot_injective

noncomputable def originalRowMasterCatalog {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) : Finset (MvPolynomial (Fin n) ℤ) :=
  {1} ∪ Finset.univ.biUnion (fun t =>
    ((T t).rows.catalog (T t).target).image (MvPolynomial.rename (T t).slot))

theorem originalRowMasterCatalog_one {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) : 1 ∈ originalRowMasterCatalog T := by
  simp [originalRowMasterCatalog]

theorem originalRowMasterCatalog_inclusion {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (t : Fin L)
    (f : MvPolynomial (Fin (T t).arity) ℤ) (hf : f ∈ (T t).rows.catalog (T t).target) :
    MvPolynomial.rename (T t).slot f ∈ originalRowMasterCatalog T := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨t, Finset.mem_univ _, Finset.mem_image.mpr ⟨f, hf, rfl⟩⟩

theorem originalRowMasterCatalog_nonzero {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) :
    ∀ f ∈ originalRowMasterCatalog T, f ≠ 0 := by
  intro f hf
  rcases Finset.mem_union.mp hf with h1 | ht
  · have hf1 : f = 1 := Finset.mem_singleton.mp h1
    rw [hf1]
    exact one_ne_zero
  · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    intro hz
    apply (T t).rows.catalog_nonzero (T t).target p hp
    apply MvPolynomial.rename_injective (T t).slot (T t).slot_injective
    simpa only [MvPolynomial.rename_zero] using hz

noncomputable def originalRowMaster {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) : MasterParameterFamily :=
  constructedMasterFamily N (originalRowMasterCatalog T) (originalRowMasterCatalog_nonzero T)

theorem originalRowMaster_conditions {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) :
    MasterParameterConditions N A (originalRowMasterCatalog T) (originalRowMaster T) :=
  constructedMasterFamily_conditions N A hA (originalRowMasterCatalog T)
    (originalRowMasterCatalog_nonzero T)

theorem originalRowData_template_conditions {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (t : Fin L) (d : ℕ)
    (hd : (T t).rowCount - 1 ≤ d) (tail : ℕ → Finset ℕ) (root : ℕ → Fin N)
    (htail : ∀ᶠ w in atTop, tail w ⊆ Finset.range ((T t).gap w).val)
    (hgap : ∀ᶠ w in atTop, ((T t).gap w).val ≤ (root w).val) :
    OriginalDualTemplateConditions (T t).template (originalRowMasterCatalog T) d tail root := by
  refine ⟨?_, hd, ?_, htail, hgap⟩
  · dsimp [OriginalPolynomialRowData.template]
    have h := (T t).rowCount_gt_one
    omega
  · intro f hf
    change f ∈ (T t).rows.catalog (T t).target at hf
    exact originalRowMasterCatalog_inclusion T t f hf

noncomputable def originalRowAndZeroTemplates {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (d₀ : ℕ) (gap₀ : ℕ → Fin N) :
    Fin (L + 1) → OriginalDualTemplate n N 1 :=
  Fin.cases (originalZeroPrimeTemplate d₀ gap₀ (fun _ => 0)) (fun t => (T t).template)

theorem originalRowAndZeroTemplates_conditions {n N L : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (d₀ d : ℕ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ d)
    (hd : ∀ t, (T t).rowCount - 1 ≤ d) (gap₀ : ℕ → Fin N)
    (tail : ℕ → Finset ℕ) (root : ℕ → Fin N)
    (htail₀ : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap₀ w).val)
    (hgap₀ : ∀ᶠ w in atTop, (gap₀ w).val ≤ (root w).val)
    (htail : ∀ t, ∀ᶠ w in atTop, tail w ⊆ Finset.range ((T t).gap w).val)
    (hgap : ∀ t, ∀ᶠ w in atTop, ((T t).gap w).val ≤ (root w).val) :
    ∀ t, OriginalDualTemplateConditions (originalRowAndZeroTemplates T d₀ gap₀ t)
      (originalRowMasterCatalog T) d tail root := by
  intro t
  refine Fin.cases ?_ (fun k => ?_) t
  · exact originalZeroPrimeTemplate_conditions d₀ d hd₀ hd₀max gap₀ (fun _ => 0)
      (originalRowMasterCatalog T) (originalRowMasterCatalog_one T) tail root htail₀ hgap₀
  · exact originalRowData_template_conditions T k d (hd k) tail root (htail k) (hgap k)

theorem originalRowAndZero_all_positive_scales_models {n N L b : ℕ}
    (T : Fin L → OriginalPolynomialRowData n N) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (d₀ d : ℕ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ d) (hd : ∀ t, (T t).rowCount - 1 ≤ d)
    (gap₀ : ℕ → Fin N) (C : ℕ → Chain b)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin b) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htail₀ : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap₀ w).val)
    (hgap₀ : ∀ᶠ w in atTop, (gap₀ w).val ≤ (root w).val)
    (htailrows : ∀ t, ∀ᶠ w in atTop, tail w ⊆ Finset.range ((T t).gap w).val)
    (hgaprows : ∀ t, ∀ᶠ w in atTop, ((T t).gap w).val ≤ (root w).val)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤ masterPredictionBlockMask (originalRowMaster T) C label w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : Fin (L + 1), ∀ j : ℕ, 1 ≤ j → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput (originalRowAndZeroTemplates T d₀ gap₀ t).arity
          (originalRowAndZeroTemplates T d₀ gap₀ t).dimension,
          u.Admissible (originalRowMaster T) C label w →
          |expectation (integerMass ((originalRowMaster T).cutoff w (root w).val) (primorial w))
            (fun y => (ρ w y - model w y) *
              (originalRowAndZeroTemplates T d₀ gap₀ t).dual (originalRowMaster T) (fun _ => j) u w y)| < η := by
  exact (originalRowMaster_conditions T A hA).finite_templates_all_positive_scales_dense_models
    (originalRowMasterCatalog_nonzero T) (originalRowAndZeroTemplates T d₀ gap₀) C hN label tail
    htail root htailroot
    (originalRowAndZeroTemplates_conditions T d₀ d hd₀ hd₀max hd gap₀ tail root htail₀ hgap₀ htailrows hgaprows)
    ρ hρ P hP

end Hindman168
