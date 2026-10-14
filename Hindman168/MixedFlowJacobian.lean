import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Genuine mixed differentiation of a C2 map on real time times state.
The spatial Jacobian's time derivative comes from symmetry of the actual
second derivative and the proved time-velocity identity near the state. -/

namespace Hindman168
open Function Set Filter Topology
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem mixedFlowJacobian_hasDerivAt {f : ℝ × E → F} {V : E → F} {z : E}
    (hf : ContDiffAt ℝ 2 f (0, z))
    (hV : ∀ᶠ y in 𝓝 z, fderiv ℝ f (0, y) (1, 0) = V y) (w : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (t, z) (0, w)) (fderiv ℝ V z w) 0 := by
  let D := fderiv ℝ f
  let DD := fderiv ℝ D (0, z)
  have hD : HasFDerivAt D DD (0, z) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have ht := hD.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 z))
  have htw := ht.clm_apply (hasDerivAt_const (0 : ℝ) (0, w))
  have hz := hD.comp z ((hasFDerivAt_const (0 : ℝ) z).prodMk (hasFDerivAt_id z))
  have hzv := hz.clm_apply (hasFDerivAt_const (1, (0 : E)) z)
  have heq : V =ᶠ[𝓝 z] (fun y => ((D ∘ Prod.mk 0) y) (1, 0)) := by
    filter_upwards [hV] with y hy
    exact hy.symm
  have hzV := hzv.congr_of_eventuallyEq heq
  have he := congrArg (fun L : E →L[ℝ] F => L w) hzV.fderiv
  have he' : fderiv ℝ V z w = DD (0, w) (1, 0) := by
    simpa only [ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply, map_zero, add_zero, zero_add] using he
  have hsym := (hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])).eq
    (1, (0 : E)) (0, w)
  convert! htw using 1
  simp only [map_zero, add_zero]
  exact he'.trans hsym.symm

end Hindman168
