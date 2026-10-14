import Hindman168.AlignmentShortCutoffGeometry
import Hindman168.FiniteSupportedEventComparison

namespace Hindman168
open FiniteMass Filter
open scoped Topology Classical

theorem alignment_short_cutoff_failure_tendsto
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (T : Finset (Fin n)) :
    Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => ¬ alignmentShortCutoffGood F w i T x)) atTop (𝓝 0) := by
  have hc : (1 : ℝ) ≤ 2 ^ T.card := one_le_pow₀ (by norm_num)
  have hp := master_alignedSqrt_failedCutoffShortBin_tendsto hF (fun _ => i)
    (fun w => (F.modulus w : ℕ)) (fun _ => 1) hc
    (Eventually.of_forall (fun _ => by norm_num))
  have hglobal : Tendsto (fun w => event (globalRawMass (F.cutoff w) (primorial w) n)
      (fun x => failedCutoffShortBin (F.cutoff w i.val)
        (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) 1 (2 ^ T.card) (x i)))
      atTop (𝓝 0) := by
    apply hp.congr'
    filter_upwards [hF.raw_cutoffs_valid] with w hw
    symm
    exact event_piMass_coordinate _
      (fun j : Fin n => rawMass_total (hw j.val (Finset.mem_range.mpr j.isLt)).2.2) i _
  apply squeeze_zero' _ _ hglobal
  · filter_upwards [alignmentGlobalRawMass_geometry hF] with w hw
    exact event_nonneg _ _ hw.1
  · filter_upwards [alignmentGlobalRawMass_geometry hF,
      master_microcell_eventually_positive hF (fun _ => i)] with w hw hR
    apply event_mono_on_support _ _ _ hw.1
    intro x hx hbad
    exact alignment_short_cutoff_failure_normalized F w i T x
      (fun j _ => alignmentGlobalRawMass_support_positive hF w x hx j) hR hbad

end Hindman168
