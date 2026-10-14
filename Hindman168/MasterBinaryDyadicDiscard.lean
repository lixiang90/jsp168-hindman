import Hindman168.BinaryDyadicCutoffDiscard
import Hindman168.MasterShortBinCutoffDiscard
import Hindman168.AlignmentRawArrayStability

namespace Hindman168

open FiniteMass Filter
open scoped BigOperators Topology Classical

theorem master_binaryDyadic_cutoff_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) :
    Tendsto (fun w => event (rawMass (F.cutoff w i.val) (primorial w))
      (fun p => ¬ binaryDyadicCutoffGood (F.cutoff w i.val) p)) atTop (𝓝 0) := by
  have hX : Tendsto (fun w => (F.cutoff w i.val : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hF.cutoff_tendsto i.val)
  have hgap := hF.cell_width_cutoff_ratio_tendsto (fun _ => i) (fun _ => i)
    (Eventually.of_forall (fun _ => le_rfl))
  have hWX : Tendsto (fun w => (primorial w : ℝ) / F.cutoff w i.val) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hgap
    filter_upwards [hF.primorial_le_modulus, hF.auxiliary_le_gap_eventually (fun _ => i)] with w hw hg
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hw.trans ((F.modulus_le_auxiliary w i.val).trans hg)
  exact rawMass_binaryDyadic_cutoff_tendsto _ _ hX hWX (Eventually.of_forall primorial_pos)

theorem master_global_binaryDyadic_coordinate_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ binaryDyadicCutoffGood (F.cutoff w i.val) (x i))) atTop (𝓝 0) := by
  apply (master_binaryDyadic_cutoff_tendsto hF i).congr'
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have ht (j : Fin n) := rawMass_total (hw j.val (Finset.mem_range.mpr j.isLt)).2.2
  symm
  rw [event_eq_expectation, event_eq_expectation, globalRawMass]
  convert expectation_piMass_coordinate _ ht i
    (fun p => if ¬ binaryDyadicCutoffGood (F.cutoff w i.val) p then (1 : ℝ) else 0) using 1
  all_goals
    congr 1
    funext x
    split_ifs <;> rfl

theorem master_global_binaryDyadic_discard_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (S : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ∃ j ∈ S, ¬ binaryDyadicCutoffGood (F.cutoff w j.val) (x j))) atTop (𝓝 0) := by
  have hs := tendsto_finsetSum S (fun j _ => master_global_binaryDyadic_coordinate_tendsto hF j)
  simp only [Finset.sum_const_zero] at hs
  apply squeeze_zero' _ _ hs
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_union_bound _ S _ hw.1

end Hindman168
