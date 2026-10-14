import Hindman168.FinitePivotCoordinates
import Hindman168.FiniteConditionalLikelihood
import Hindman168.HarmonicCutoffBands
import Hindman168.GlobalChainLaw
import Hindman168.AlignmentNumericalPolynomialBounds

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

noncomputable def alignmentOutsideRawMass {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) : Mass ({j : Fin n // j ≠ i} → ℕ) :=
  piMass (fun j => rawMass (F.cutoff w j.val.val) (primorial w))

theorem alignment_block_insert_pivot {n : ℕ} (i : Fin n)
    (x : {j : Fin n // j ≠ i} → ℕ) (p q : ℕ) (T : Finset (Fin n))
    (hT : ∀ j ∈ T, j < i) :
    alignmentNaturalBlockProduct (insertPivotCoordinate i x p) T =
      alignmentNaturalBlockProduct (insertPivotCoordinate i x q) T := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [insertPivotCoordinate, dif_neg (ne_of_lt (hT j hj))]

theorem alignment_raw_pivot_event {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (E : (Fin n → ℕ) → Prop) :
    event (globalRawMass (F.cutoff w) (primorial w) n) E =
      event (conditionalJoint (alignmentOutsideRawMass F w i)
        (fun _ => rawMass (F.cutoff w i.val) (primorial w)))
        (fun xp => E (insertPivotCoordinate i xp.1 xp.2)) := by
  rw [event_eq_expectation, event_eq_expectation, expectation_conditionalJoint]
  convert expectation_piMass_pivot (fun j : Fin n => rawMass (F.cutoff w j.val) (primorial w))
    i (fun x => if E x then 1 else 0) using 1 <;> congr 1
  unfold alignmentOutsideRawMass
  congr 1
  exact Subsingleton.elim _ _

theorem alignmentOutsideRawMass_geometry
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) :
    ∀ᶠ w in atTop, (∀ x, 0 ≤ alignmentOutsideRawMass F w i x) ∧
      total (alignmentOutsideRawMass F w i) = 1 ∧
      ∀ x ∈ (alignmentOutsideRawMass F w i).support, ∀ j : Fin n, j < i →
        0 < insertPivotCoordinate i x 1 j ∧
        insertPivotCoordinate i x 1 j ≤ F.cutoff w j.val ^ 2 ∧
        Nat.Coprime (insertPivotCoordinate i x 1 j) (primorial w) := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have hz (j : Fin n) := (hw j.val (Finset.mem_range.mpr j.isLt)).2.2
  refine ⟨piMass_nonneg _ (fun j p => ?_), piMass_total_one _ (fun j => rawMass_total (hz j.val)), ?_⟩
  · rw [rawMass_apply]
    exact harmonicWeight_nonneg (hz j.val) p
  · intro x hx j hj
    have hne : alignmentOutsideRawMass F w i x ≠ 0 := Finsupp.mem_support_iff.mp hx
    rw [alignmentOutsideRawMass, piMass_apply] at hne
    have hs := Finsupp.mem_support_iff.mpr
      (Finset.prod_ne_zero_iff.mp hne ⟨j, ne_of_lt hj⟩ (Finset.mem_univ _))
    have hh := Finset.mem_filter.mp (rawMass_support_window _ _ hs)
    have hb := Finset.mem_Ico.mp hh.1
    simp only [insertPivotCoordinate, dif_neg (ne_of_lt hj)]
    exact ⟨lt_of_lt_of_le (hF.cutoff_positive w j.val) hb.1, hb.2.le, hh.2⟩

end Hindman168
