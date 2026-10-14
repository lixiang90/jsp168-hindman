import Hindman168.NativeCentralFactorMetric
import Hindman168.NativeCenterQuotientDimension

/-! GENUINE lower-step native data for ORIGINAL G/center and ORIGINAL image lattice. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeCentralQuotientData {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    NativeNilmanifoldData.{u} (s-1) := by
  let F := D.E ⧸ nativeLieCenterModel (I := D.I) (G := D.G)
  let Q := D.G ⧸ Subgroup.center D.G
  letI := nativeCenterQuotientChartedSpace (I := D.I) (G := D.G)
  letI := nativeCenterQuotient_t2Space (I := D.I) (G := D.G)
  letI := nativeCenterQuotient_lieGroup (I := D.I) (G := D.G)
  letI := nativeCenterQuotient_simplyConnected (I := D.I) (G := D.G)
  letI := nativeLattice_center_quotient_image_discrete (I := D.I) D.Γ
  letI := native_central_factor_compact D
  exact {
    E := F
    H := F
    I := 𝓘(ℝ, F)
    G := Q
    rationalModule := Module.compHom F (algebraMap ℚ ℝ)
    step_le := by
      rw [Group.nilpotencyClass_quotient_center]
      exact Nat.sub_le_sub_right D.step_le 1
    Γ := D.Γ.map (QuotientGroup.mk' (Subgroup.center D.G))
    metric := nativeCentralFactorMetric D
    metric_quotientMap := native_central_factor_metric_quotientMap D }

theorem native_central_quotient_data_group {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeCentralQuotientData D).G = (D.G ⧸ Subgroup.center D.G) := rfl

theorem native_central_quotient_data_model {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeCentralQuotientData D).E = (D.E ⧸ nativeLieCenterModel (I := D.I) (G := D.G)) := rfl

theorem native_central_quotient_data_dimension_lt {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    [Nontrivial D.G] : Module.finrank ℝ (nativeCentralQuotientData D).E < Module.finrank ℝ D.E :=
  nativeCenterQuotientModel_finrank_lt (I := D.I) (G := D.G)

end Hindman168
