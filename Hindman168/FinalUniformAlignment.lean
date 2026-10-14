import Hindman168.SelectedAlignmentScheduleFinal
import Hindman168.FinalUniformAlignmentInput

/-! The uniform selected Alignment principle is proved from the original
represented model family. All finite data and the positive mass budget are
chosen before master parameters, selected gaps, observers and thresholds. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology
universe u

theorem hasUniformSelectedPrincipalAlignment : HasUniformSelectedPrincipalAlignment.{u} := by
  intro n r s
  obtain ⟨B,A,hB,hBpos,hA,hclosed,δ,hδ,hlim⟩ := selected_alignment_finite_data_mass.{u} n r s
  refine ⟨B,A,hclosed,hB,hBpos,hA,δ,hδ,?_⟩
  intro d M hM Poly F hF e heM S hS _hunit θ hθ
  apply hlim d M Poly F hF e heM S _ θ hθ
  intro T i γ
  have hgap : masterGapIndex M hM (energyPadding e i) =
      (fun _ => (⟨energyPadding e i,heM _⟩ : Fin M)) := by
    funext w
    apply Fin.ext
    exact masterGapIndex_val M hM _ w (heM _)
  simpa only [hgap] using hS T i γ

end Hindman168
