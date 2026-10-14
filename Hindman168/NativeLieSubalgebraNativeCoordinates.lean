import Hindman168.RoughNativeSubgroupNilmanifold
import Hindman168.HomeomorphSingletonDifferential
import Hindman168.LieExponentialHomomorphism

namespace Hindman168
open Function
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
attribute [local instance] lieGroup_smooth_min_three

theorem nativeLieSubalgebra_inclusion_mfderiv (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    mfderiv 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) I
      ((↑) : nativeLieSubalgebraSubgroup (E := E) S → G) 1 =
      (nativeLieSubalgebraModel (E := E) S).subtype.toContinuousLinearMap := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_isManifold S
  let T := nativeLieSubalgebraModel (E := E) S
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let J := 𝓘(ℝ, T)
  let e := nativeLieSubalgebraExponentialDiffeomorph (E := E) S
  let f : L → G := (↑)
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  let π : T →L[ℝ] E := T.subtype.toContinuousLinearMap
  have hf : MDifferentiableAt J I f (e 0) :=
    (nativeLieSubalgebra_inclusion_contMDiff S).mdifferentiableAt (by norm_num)
  have he : MDifferentiableAt J J e 0 := e.contMDiff_toFun.mdifferentiableAt (by norm_num)
  have hpsmooth : ContMDiff J 𝓘(ℝ,E) ∞ π := π.contDiff.contMDiff
  have hp : MDifferentiableAt J 𝓘(ℝ,E) π 0 := hpsmooth.mdifferentiableAt (by norm_num)
  have hx : MDifferentiableAt 𝓘(ℝ,E) I exp (π 0) :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hfun : f ∘ e = exp ∘ π := rfl
  have he0 : e (0 : T) = 1 := by
    apply Subtype.ext
    exact nativeLieExponential_zero (I := I) (G := G)
  have hed : mfderiv J J e 0 = ContinuousLinearMap.id ℝ T :=
    homeomorphSingleton_mfderiv (nativeLieSubalgebraExponentialHomeomorph (E := E) S) 0
  have hd := mfderiv_comp (0 : T) hf he
  rw [hfun, he0, hed] at hd
  have hd' : mfderiv J I (exp ∘ π) 0 = mfderiv J I f 1 :=
    hd.trans (ContinuousLinearMap.comp_id (mfderiv J I f 1 : T →L[ℝ] E))
  have hr := mfderiv_comp (0 : T) hx hp
  have hxd : mfderiv 𝓘(ℝ,E) I exp (π 0) = ContinuousLinearMap.id ℝ E := by
    rw [π.map_zero]
    exact nativeLieExponential_mfderiv_zero (I := I) (G := G)
  have hpd : mfderiv J 𝓘(ℝ,E) π 0 = π := π.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hxd, hpd] at hr
  have hr' : mfderiv J I (exp ∘ π) 0 = π := hr.trans (ContinuousLinearMap.id_comp π)
  exact hd'.symm.trans hr'

theorem nativeLieSubalgebra_native_exponential (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := nativeLieSubalgebra_boundaryless S
    ∀ v : nativeLieSubalgebraModel (E := E) S,
      nativeLieExponential (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S))
        (G := nativeLieSubalgebraSubgroup (E := E) S) v =
      nativeLieSubalgebraExponentialHomeomorph (E := E) S v := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  intro v
  apply Subtype.ext
  have hf : MDifferentiable 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) I
      ((↑) : nativeLieSubalgebraSubgroup (E := E) S → G) :=
    (nativeLieSubalgebra_inclusion_contMDiff S).mdifferentiable (by norm_num)
  have h := nativeLieExponential_map
    (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)) (J := I)
    (nativeLieSubalgebraSubgroup (E := E) S).subtype hf v
  change (nativeLieExponential (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S))
    (G := nativeLieSubalgebraSubgroup (E := E) S) v).val =
    nativeLieExponential (I := I) (G := G)
      ((mfderiv 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S) I
        ((↑) : nativeLieSubalgebraSubgroup (E := E) S → G) 1) v) at h
  rw [nativeLieSubalgebra_inclusion_mfderiv S] at h
  exact h

theorem nativeLieSubalgebra_native_logarithm (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) :
    letI := nativeLieSubalgebraChartedSpace (E := E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := nativeLieSubalgebra_boundaryless S
    letI := nativeLieSubalgebraSubgroup_connected S
    letI := nativeLieSubalgebraSubgroup_simplyConnected S
    ∀ g : nativeLieSubalgebraSubgroup (E := E) S,
      (nativeLieGlobalLogarithm (E := nativeLieSubalgebraModel (E := E) S)
          (I := 𝓘(ℝ, nativeLieSubalgebraModel (E := E) S)) g : E) =
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val := by
  letI := nativeLieSubalgebraChartedSpace (E := E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  letI := nativeLieSubalgebraSubgroup_connected S
  letI := nativeLieSubalgebraSubgroup_simplyConnected S
  let T := nativeLieSubalgebraModel (E := E) S
  let L := nativeLieSubalgebraSubgroup (E := E) S
  let e := nativeLieSubalgebraExponentialHomeomorph (E := E) S
  intro g
  have h := nativeLieExponential_globalLogarithm (E := T) (I := 𝓘(ℝ,T)) (G := L) g
  rw [nativeLieSubalgebra_native_exponential S] at h
  have he : nativeLieGlobalLogarithm (E := T) (I := 𝓘(ℝ,T)) (G := L) g = e.symm g :=
    e.injective (h.trans (e.apply_symm_apply g).symm)
  exact congrArg ((↑) : T → E) he

end Hindman168
