import Hindman168.CompleteResidueCellMass
import Hindman168.FiniteSetConditionDomination
import Hindman168.FinitePositiveConditioningLimit

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- Actual original harmonic conditioning on a complete microcell/residue
fiber differs from its uniform progression law by at most cellWidth/X.
The harmonic normalizer cancels exactly, rather than being approximated. -/
theorem principal_complete_cell_harmonic_event_error
    (X W M q : ℕ) (k : ℤ) (r : Fin M)
    (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M)
    (hr : r.val.Coprime W) (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)) (P : ℤ → Prop) :
    |event (conditionMass (integerMass X W)
        (fun y => y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val)) P -
      finiteHaarMean (fun t : Fin q => if P (completeResidueCellPoint k M q r t) then 1 else 0)| ≤
        (M * q : ℕ) / (X : ℝ) := by
  let S := intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val
  let f : ℤ → ℝ := fun y => if P y then 1 else 0
  have hn : event (integerMass X W) (fun y => y ∈ S ∧ P y) =
      ∑ y ∈ S, integerMass X W y * f y := by
    rw [show (fun y => y ∈ S ∧ P y) = (fun y => y ∈ S.filter P) by
      funext y; simp]
    rw [event_finset_mem, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    simp only [f]
    split_ifs <;> simp
  have hd : event (integerMass X W) (fun y => y ∈ S) =
      ∑ y ∈ S, integerMass X W y * (1 : ℝ) := by simp [event_finset_mem]
  have hn' := completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi f
  have hd' := completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi (fun _ => 1)
  simp only [if_pos hr, mul_one] at hn' hd'
  have hid : event (conditionMass (integerMass X W) (fun y => y ∈ S)) P =
      (∑ t : Fin q, (1 / (completeResidueCellPoint k M q r t : ℝ)) * f (completeResidueCellPoint k M q r t)) /
      (∑ t : Fin q, 1 / (completeResidueCellPoint k M q r t : ℝ)) := by
    rw [finite_condition_event_inter, hn, hd]
    simp only [mul_one]
    rw [hn', hd']
    field_simp [hZ.ne']
  change |event (conditionMass (integerMass X W) (fun y => y ∈ S)) P - _| ≤ _
  rw [hid]
  have hXR : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  have hAR : (X : ℝ) ≤ (k : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo
  have he := completeResidueCell_harmonic_error k M q hM hq r f
    (fun y => by simp only [f]; split_ifs <;> norm_num) (hXR.trans_le hAR)
  rw [completeResidueCell_sum k M q hM, completeResidueCell_sum k M q hM] at he
  exact he.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hXR hAR)
end Hindman168
