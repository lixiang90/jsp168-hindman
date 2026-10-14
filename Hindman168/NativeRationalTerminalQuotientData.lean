import Hindman168.NativeRationalTerminalQuotientMetric
import Hindman168.NativeRationalTerminalQuotientStructures

/-! Actual original native terminal quotient structures/model/image lattice/metric for ANY finite rational Lie filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeRationalTerminalQuotientData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) : NativeNilmanifoldData.{u} s := by
  letI := native_rational_terminal_subgroup_normal D F
  letI : IsClosed ((F.layer ℓ) : Set D.E) :=
    native_rational_terminal_model_closed D F
  let EQ := D.E ⧸ (F.layer ℓ)
  let Q := D.G ⧸ nativeRationalTerminalSubgroup D F
  letI := nativeRationalTerminalQuotientChartedSpace D F
  letI := native_rational_terminal_quotient_lieGroup D F
  letI := native_rational_terminal_quotient_boundaryless D F
  letI := native_rational_terminal_quotient_t2Space D F
  letI := native_rational_terminal_quotient_simplyConnected D F
  letI := native_rational_terminal_image_lattice_discrete D F
  letI := native_rational_terminal_image_lattice_cocompact D F
  exact {
    E := EQ
    H := EQ
    I := 𝓘(ℝ,EQ)
    G := Q
    charted := nativeRationalTerminalQuotientChartedSpace D F
    lie := native_rational_terminal_quotient_lieGroup D F
    boundaryless := native_rational_terminal_quotient_boundaryless D F
    rationalModule := Module.compHom EQ (algebraMap ℚ ℝ)
    step_le := (Group.nilpotencyClass_quotient_le (nativeRationalTerminalSubgroup D F)).trans
      D.step_le
    Γ := D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))
    metric := nativeRationalTerminalQuotientMetric D F
    metric_quotientMap := native_rational_terminal_quotient_metric_quotientMap D F }

theorem native_rational_terminal_quotient_data_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeRationalTerminalQuotientData D F).G =
      (D.G ⧸ nativeRationalTerminalSubgroup D F) := rfl

theorem native_rational_terminal_quotient_data_model {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeRationalTerminalQuotientData D F).E =
      (D.E ⧸ (F.layer ℓ)) := rfl

theorem native_rational_terminal_quotient_data_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    (nativeRationalTerminalQuotientData D F).Γ = D.Γ.map
      (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F)) := rfl

end Hindman168
