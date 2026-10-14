import Hindman168.NativeRationalCubeMetric
import Hindman168.NativeLieSubalgebraLieGroup

/-! Genuine native cube-subgroup data with original lattice intersection
and original step bound. No loss of step or matrix replacement. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

attribute [local instance] nativeFiniteProductRationalModule


attribute [local instance] nativeFiniteProduct_topologicalGroup

theorem native_finite_product_original_step {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) :
    Group.nilpotencyClass (nativeFiniteProduct D.G n) ≤ s := by
  induction n with
  | zero => exact D.step_le
  | succ n ih => exact productGroup_nilpotencyClass_le s ih D.step_le

noncomputable def nativeRationalCubeData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : NativeNilmanifoldData.{u} s := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  let S := nativeRationalCubeNativeAlgebra D F d n e
  let T := nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n) S
  let L := nativeRationalCubeSubgroup D F d n e
  letI : TopologicalSpace (T : Type u) :=
    (inferInstance : NormedAddCommGroup (T : Type u)).toUniformSpace.toTopologicalSpace
  letI : ChartedSpace T L := nativeLieSubalgebraChartedSpace (E := nativeFiniteProduct D.E n) S
  letI : LieGroup 𝓘(ℝ,T) ∞ L := nativeLieSubalgebra_lieGroup S
  letI : BoundarylessManifold 𝓘(ℝ,T) L := nativeLieSubalgebra_boundaryless S
  letI hTop : IsTopologicalGroup L := topologicalGroup_of_lieGroup 𝓘(ℝ,T) (minSmoothness ℝ 3)
  letI := nativeLieSubalgebraSubgroup_connected S
  letI := nativeLieSubalgebraSubgroup_simplyConnected S
  letI : Module ℚ T := Module.compHom T (algebraMap ℚ ℝ)
  letI := native_rational_cube_lattice_discrete D F d n e
  letI := native_rational_cube_lattice_compact D F d n e
  exact {
    E := T
    H := T
    I := 𝓘(ℝ,T)
    G := L
    groupTopology := inferInstanceAs (TopologicalSpace L)
    group := inferInstanceAs (Group L)
    topologicalGroup := hTop
    connected := nativeLieSubalgebraSubgroup_connected S
    simplyConnected := nativeLieSubalgebraSubgroup_simplyConnected S
    charted := nativeLieSubalgebraChartedSpace (E := nativeFiniteProduct D.E n) S
    lie := nativeLieSubalgebra_lieGroup S
    boundaryless := nativeLieSubalgebra_boundaryless S
    step_le := (Subgroup.nilpotencyClass_le L).trans (native_finite_product_original_step D n)
    Γ := (nativeFiniteProductLattice D.Γ n).comap L.subtype
    metric := nativeRationalCubeMetric D F d n e
    metric_quotientMap := native_rational_cube_metric_quotientMap D F d n e }

theorem native_rational_cube_data_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeData D F d n e).G = nativeRationalCubeSubgroup D F d n e := rfl

theorem native_rational_cube_data_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeData D F d n e).Γ =
      (nativeFiniteProductLattice D.Γ n).comap (nativeRationalCubeSubgroup D F d n e).subtype := rfl

end Hindman168
