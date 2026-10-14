import Hindman168.NativeDiagonalFactorMetric
import Hindman168.NativeDiagonalQuotientStructures

/-! GENUINE native data for the ORIGINAL product group modulo ACTUAL
diagonal center, with original image lattice/model quotient/compatible metric.
The proved step bound is the SAME s, not an assumed reduction. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] diagonal_center_normal

noncomputable def nativeDiagonalQuotientData {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    NativeNilmanifoldData.{u} s := by
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  let F := (D.E × D.E) ⧸ nativeDiagonalCenterModel D
  let Q := (D.G × D.G) ⧸ diagonalCenterSubgroup D.G
  letI := nativeDiagonalQuotientChartedSpace D
  letI := native_diagonal_quotient_lieGroup D
  letI := native_diagonal_quotient_boundaryless D
  letI := native_diagonal_quotient_t2Space D
  letI := native_diagonal_quotient_simplyConnected D
  letI := native_diagonal_quotient_lattice_discrete D
  letI := native_diagonal_quotient_lattice_cocompact D
  exact {
    E := F
    H := F
    I := 𝓘(ℝ, F)
    G := Q
    charted := nativeDiagonalQuotientChartedSpace D
    lie := native_diagonal_quotient_lieGroup D
    boundaryless := native_diagonal_quotient_boundaryless D
    rationalModule := Module.compHom F (algebraMap ℚ ℝ)
    step_le := (Group.nilpotencyClass_quotient_le (diagonalCenterSubgroup D.G)).trans
      (productGroup_nilpotencyClass_le s D.step_le D.step_le)
    Γ := (D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G))
    metric := nativeDiagonalFactorMetric D
    metric_quotientMap := native_diagonal_factor_metric_quotientMap D }

theorem native_diagonal_quotient_data_group {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeDiagonalQuotientData D).G = ((D.G × D.G) ⧸ diagonalCenterSubgroup D.G) := rfl

theorem native_diagonal_quotient_data_model {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeDiagonalQuotientData D).E = ((D.E × D.E) ⧸ nativeDiagonalCenterModel D) := rfl

theorem native_diagonal_quotient_data_lattice {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeDiagonalQuotientData D).Γ =
      (D.Γ.prod D.Γ).map (QuotientGroup.mk' (diagonalCenterSubgroup D.G)) := rfl

end Hindman168
