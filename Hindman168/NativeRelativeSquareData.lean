import Hindman168.NativeRelativeSquareStructures
import Hindman168.NativeRelativeSquareMetric

/-! GENUINE NativeData(s) for EXACT ORIGINAL relative-square group,
ACTUAL relative product model, ORIGINAL restricted lattice and actual metric.
All structural/rational/lattice inputs are proved; SAME step bound s only. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeSquareData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) : NativeNilmanifoldData.{u} s := by
  let T := nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i)
  let L := nativeRelativeSquareFiltration D d i
  letI := nativeRelativeSquareChartedSpace D d i
  letI := native_relative_square_lieGroup D d i
  letI := native_relative_square_boundaryless D d i
  letI := native_relative_square_filtration_contractible D d i
  letI : Module ℚ T := Module.compHom T (algebraMap ℚ ℝ)
  letI := native_relative_square_lattice_discrete D d i
  letI := native_relative_square_lattice_cocompact D d hd i
  exact {
    E := T
    H := T
    I := 𝓘(ℝ,T)
    G := L
    charted := nativeRelativeSquareChartedSpace D d i
    lie := native_relative_square_lieGroup D d i
    boundaryless := native_relative_square_boundaryless D d i
    rationalModule := Module.compHom T (algebraMap ℚ ℝ)
    step_le := (Subgroup.nilpotencyClass_le L).trans (productGroup_nilpotencyClass_le s D.step_le D.step_le)
    Γ := (D.Γ.prod D.Γ).comap L.subtype
    metric := nativeRelativeSquareMetric D d hd i
    metric_quotientMap := native_relative_square_metric_quotientMap D d hd i }

theorem native_relative_square_data_group {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeRelativeSquareData D d hd i).G = nativeRelativeSquareFiltration D d i := rfl

theorem native_relative_square_data_model {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeRelativeSquareData D d hd i).E = nativeRelativeSquareModel D d i := by
  change (nativeLieSubalgebraModel (nativeRelativeSquareNativeLieAlgebra D d i) : Type u) = _
  exact congrArg (fun V : Submodule ℝ (D.E × D.E) => (V : Type u))
    (native_relative_square_native_model_eq D d i)

theorem native_relative_square_data_lattice {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeRelativeSquareData D d hd i).Γ =
      (D.Γ.prod D.Γ).comap (nativeRelativeSquareFiltration D d i).subtype := rfl

end Hindman168
