import Hindman168.LieInvariantCoordinateField
import Hindman168.EquilibriumPicardFlow

/-! A constructed parameter-differentiable coordinate flow for the
actual native invariant field, near the zero Lie-algebra parameter.
The field derivative and its square-zero property are proved inputs,
not supplied exponential regularity or caller-provided flow data. -/

namespace Hindman168
open Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I (minSmoothness ℝ 3) G] [BoundarylessManifold I G]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 noncomputable def lieCoordinateParametricFlow (v : E) : C(Icc a b, E × E) :=
  curvePicardImplicit hab t₀
    (lieFrozenCoordinateField_hasStrictFDerivAt (I := I) (G := G))
    (lieFrozenCoordinateLinearization_square_zero (E := E))
    (v, extChartAt I (1 : G) (1 : G))

 theorem lieCoordinateParametricFlow_zero :
    lieCoordinateParametricFlow (I := I) (G := G) hab t₀ (0 : E) =
      ContinuousMap.const (Icc a b) (0, extChartAt I (1 : G) (1 : G)) :=
  curvePicardImplicit_self hab t₀ _ _

 theorem lieCoordinateParametricFlow_endpoint_hasStrictFDerivAt (t : Icc a b) :
    HasStrictFDerivAt (fun v : E => lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t)
      ((ContinuousLinearMap.id ℝ E).prod
        (((t : ℝ) - t₀) • ContinuousLinearMap.id ℝ E)) (0 : E) := by
  have hd := (curvePicardImplicit_endpoint_hasStrictFDerivAt hab t₀
    (lieFrozenCoordinateField_hasStrictFDerivAt (I := I) (G := G))
    (lieFrozenCoordinateLinearization_square_zero (E := E)) t).comp (0 : E)
    ((hasStrictFDerivAt_id (𝕜 := ℝ) (0 : E)).prodMk
      (hasStrictFDerivAt_const (𝕜 := ℝ) (extChartAt I (1 : G) (1 : G)) (0 : E)))
  apply hd.congr_fderiv
  ext v <;> simp [lieFrozenCoordinateLinearization]

 theorem lieCoordinateParametricFlow_state_endpoint_hasStrictFDerivAt (t : Icc a b) :
    HasStrictFDerivAt (fun v : E => (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t).2)
      (((t : ℝ) - t₀) • ContinuousLinearMap.id ℝ E) (0 : E) := by
  exact (lieCoordinateParametricFlow_endpoint_hasStrictFDerivAt (I := I) (G := G) hab t₀ t).snd

 theorem lieCoordinateParametricFlow_eventually_integral :
    ∀ᶠ v : E in 𝓝 0,
      lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v t₀ =
        (v, extChartAt I (1 : G) (1 : G)) ∧
      ∀ t ∈ Ioo a b, HasDerivAt
        (curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v))
        (lieFrozenCoordinateField (I := I) (G := G)
          (curveClippedExtension hab (lieCoordinateParametricFlow (I := I) (G := G) hab t₀ v) t)) t := by
  have he := curvePicardImplicit_eventually_integral hab t₀
    (lieFrozenCoordinateField_hasStrictFDerivAt (I := I) (G := G))
    (lieFrozenCoordinateLinearization_square_zero (E := E))
    (lieFrozenCoordinateField_equilibrium (I := I) (G := G))
  exact (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually he

end Hindman168
