import Hindman168.NativeRationalRelativeStructures
import Hindman168.NativeRationalRelativeMetric

/-! Genuine native structures and original lattice quotient for arbitrary finite rational Lie-filtered relative layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) : NativeNilmanifoldData.{u} s := by
  let T := nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i)
  let L := nativeRationalRelativeGroupLayer D F i
  letI := nativeRationalRelativeChartedSpace D F i
  letI := native_rational_relative_lieGroup D F i
  letI := native_rational_relative_boundaryless D F i
  letI := native_rational_relative_contractible D F i
  letI : Module ℚ T := Module.compHom T (algebraMap ℚ ℝ)
  letI := native_rational_relative_lattice_discrete D F i
  letI := native_rational_relative_lattice_cocompact D F i
  exact {
    E := T
    H := T
    I := 𝓘(ℝ,T)
    G := L
    charted := nativeRationalRelativeChartedSpace D F i
    lie := native_rational_relative_lieGroup D F i
    boundaryless := native_rational_relative_boundaryless D F i
    rationalModule := Module.compHom T (algebraMap ℚ ℝ)
    step_le := (Subgroup.nilpotencyClass_le L).trans (productGroup_nilpotencyClass_le s D.step_le D.step_le)
    Γ := (D.Γ.prod D.Γ).comap L.subtype
    metric := nativeRationalRelativeMetric D F i
    metric_quotientMap := native_rational_relative_metric_quotientMap D F i }

theorem native_rational_relative_data_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeRationalRelativeData D F i).G = nativeRationalRelativeGroupLayer D F i := rfl

theorem native_rational_relative_data_model {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeRationalRelativeData D F i).E = relativeLinearFiltration F.layer i := by
  change (nativeLieSubalgebraModel (nativeRationalRelativeNativeSubalgebra D F i) : Type u) = _
  exact congrArg (fun V : Submodule ℝ (D.E × D.E) => (V : Type u))
    (native_rational_relative_subalgebra_model D F i)

theorem native_rational_relative_data_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    (nativeRationalRelativeData D F i).Γ =
      (D.Γ.prod D.Γ).comap (nativeRationalRelativeGroupLayer D F i).subtype := rfl

end Hindman168
