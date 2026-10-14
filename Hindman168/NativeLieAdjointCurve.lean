import Hindman168.NativeLieAdjointSmooth
import Hindman168.NativeLieAdjointEquiv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The actual operator-valued adjoint curve has its genuine infinitesimal
generator and satisfies a linear differential equation. The generator is
defined by its actual derivative, not supplied as a Lie-bracket operator.
Identifying that generator with the native bracket remains separate work. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 noncomputable def nativeLieAdjointCurve (v : E) (t : ℝ) : E →L[ℝ] E :=
  nativeLieAdjoint (I := I) (lieOneParameterCurve (I := I) (G := G) v t)

 theorem nativeLieAdjointCurve_zero (v : E) :
    nativeLieAdjointCurve (I := I) (G := G) v 0 = 1 := by
  rw [nativeLieAdjointCurve, lieOneParameterCurve_zero, nativeLieAdjoint_one]
  rfl

 theorem nativeLieAdjointCurve_add (v : E) (r s : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v (r + s) =
      nativeLieAdjointCurve (I := I) (G := G) v r * nativeLieAdjointCurve (I := I) (G := G) v s := by
  simp only [nativeLieAdjointCurve, lieOneParameterCurve_add, nativeLieAdjoint_mul]
  rfl

 theorem nativeLieAdjointCurve_contDiff (v : E) :
    ContDiff ℝ ∞ (nativeLieAdjointCurve (I := I) (G := G) v) := by
  have he : ContMDiff 𝓘(ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞ (fun t : ℝ => (v, t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hc := (lieOneParameterCurve_joint_contMDiff (I := I) (G := G)).comp he
  have ha := (nativeLieAdjoint_contMDiff (I := I) (G := G)).comp hc
  rw [contMDiff_iff_contDiff] at ha
  exact ha

 noncomputable def nativeLieAdjointGenerator (v : E) : E →L[ℝ] E :=
  deriv (nativeLieAdjointCurve (I := I) (G := G) v) 0

 theorem nativeLieAdjointCurve_hasDerivAt_zero (v : E) :
    HasDerivAt (nativeLieAdjointCurve (I := I) (G := G) v)
      (nativeLieAdjointGenerator (I := I) (G := G) v) 0 :=
  ((nativeLieAdjointCurve_contDiff (I := I) (G := G) v).differentiable (by norm_num) 0).hasDerivAt

 theorem nativeLieAdjointCurve_hasDerivAt (v : E) (t : ℝ) :
    HasDerivAt (nativeLieAdjointCurve (I := I) (G := G) v)
      (nativeLieAdjointCurve (I := I) (G := G) v t * nativeLieAdjointGenerator (I := I) (G := G) v) t := by
  let A := nativeLieAdjointCurve (I := I) (G := G) v
  let B := nativeLieAdjointGenerator (I := I) (G := G) v
  have hs : HasDerivAt (fun u : ℝ => u - t) 1 t := (hasDerivAt_id t).sub_const t
  have h0 : HasDerivAt A B ((fun u : ℝ => u - t) t) := by
    simpa only [sub_self] using nativeLieAdjointCurve_hasDerivAt_zero (I := I) (G := G) v
  have hd : HasDerivAt (fun u : ℝ => A (u - t)) B t := by
    have h := h0.scomp (h := fun u : ℝ => u - t) t hs
    simp only [one_smul] at h
    convert! h using 1
  have hp := hd.const_mul (A t)
  have heq : (fun u : ℝ => A t * A (u - t)) = A := by
    funext u
    rw [← nativeLieAdjointCurve_add]
    congr 1
    abel
  rw [heq] at hp
  exact hp

end Hindman168
