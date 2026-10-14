import Hindman168.OriginalBlockProductTesting
import Hindman168.PrimeWeightedDiagonal

/-! The original global raw harmonic coordinates produce exactly the
original block-product law. Unused coordinates are integrated out with
their proved total mass one, rather than changing the sampling measure. -/

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.block_raw_product_expectation {n N : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val) :
    ∀ᶠ w in atTop, ∀ f : ℤ → ℝ,
      expectation (globalRawMass (F.cutoff w) (primorial w) N) (fun x =>
        f ((maskBlockChain T i.val hT hTi).sampleProducts
          (maskBlockChain_block_range T i hT hTi) x 0 : ℤ)) =
      expectation (originalBlockProductMass F T i.val hT hTi w) f := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro f
  let C := maskBlockChain T i.val hT hTi
  let hC := maskBlockChain_block_range T i hT hTi
  have htail (col : Fin 1) : ValidCutoffs (C.tailCutoffs (F.cutoff w) col) (primorial w) :=
    chain_tailCutoffs_valid C (F.cutoff w) (primorial w) hC
      (fun j hj => ⟨(hw j hj).1, (hw j hj).2.1⟩) col
  have htotal (col : Fin 1) : total (blockOriginal (primorial w) (C.cutoffs (F.cutoff w) col)) = 1 := by
    change total (productMass (tailMass (primorial w) (C.tailCutoffs (F.cutoff w) col))
      (F.cutoff w i.val) (primorial w)) = 1
    exact productMass_total (tailMass_total (primorial_pos w) _ (htail col))
      (hw i.val (Finset.mem_range.mpr i.isLt)).2.2
  have h := congrArg (fun ν : Mass (Fin 1 → ℕ) => expectation ν
    (fun z => f (z 0 : ℤ)))
    (global_chain_coordinate_mass C (F.cutoff w) (primorial w) hC
      (fun j => (hw j.val (Finset.mem_range.mpr j.isLt)).2.2))
  rw [expectation_push] at h
  have he := expectation_piMass_coordinate
    (fun col : Fin 1 => blockOriginal (primorial w) (C.cutoffs (F.cutoff w) col)) htotal 0
    (fun y : ℕ => f (y : ℤ))
  rw [he] at h
  rw [originalBlockProductMass, integerProductMass, expectation_push]
  exact h

theorem MasterParameterConditions.block_raw_product_event {n N : ℕ}
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val) :
    ∀ᶠ w in atTop, ∀ E : ℤ → Prop,
      event (globalRawMass (F.cutoff w) (primorial w) N) (fun x =>
        E ((maskBlockChain T i.val hT hTi).sampleProducts
          (maskBlockChain_block_range T i hT hTi) x 0 : ℤ)) =
      event (originalBlockProductMass F T i.val hT hTi w) E := by
  filter_upwards [hF.block_raw_product_expectation T i hT hTi] with w hw
  intro E
  rw [event_eq_expectation, event_eq_expectation]
  exact hw (fun y => if E y then 1 else 0)

end Hindman168
