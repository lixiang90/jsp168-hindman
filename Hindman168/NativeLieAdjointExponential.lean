import Hindman168.NativeLieAdjointCurve
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-! The original native adjoint curve is the genuine Banach-algebra
exponential of its derivative-defined generator. The proof uses its actual
global differential equation. No identification with the native Lie bracket
is assumed here. -/

namespace Hindman168
open Function Set Topology
open scoped Manifold ContDiff

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

 theorem linearODE_eq_exp {f : ℝ → A} {b : A} (h0 : f 0 = 1)
    (hf : ∀ t, HasDerivAt f (f t * b) t) (t : ℝ) :
    f t = NormedSpace.exp (t • b) := by
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let q : ℝ → A := fun u => f u * NormedSpace.exp (u • (-b))
  have hq : ∀ u, HasDerivAt q 0 u := by
    intro u
    have h := (hf u).mul (hasDerivAt_exp_smul_const' (-b) u)
    convert! h using 1
    simp only [mul_neg, neg_mul, mul_assoc, add_neg_cancel]
  have hconst : q t = q 0 :=
    is_const_of_deriv_eq_zero (fun u => (hq u).differentiableAt)
      (fun u => (hq u).deriv) t 0
  have hprod : f t * NormedSpace.exp (-(t • b)) = 1 := by
    simpa only [q, smul_neg, zero_smul, neg_zero, NormedSpace.exp_zero, h0, one_mul, mul_one]
      using hconst
  have hinv : NormedSpace.exp (-(t • b)) * NormedSpace.exp (t • b) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.refl (t • b)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  calc
    f t = f t * (NormedSpace.exp (-(t • b)) * NormedSpace.exp (t • b)) := by rw [hinv, mul_one]
    _ = (f t * NormedSpace.exp (-(t • b))) * NormedSpace.exp (t • b) := (mul_assoc _ _ _).symm
    _ = NormedSpace.exp (t • b) := by rw [hprod, one_mul]

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointCurve_eq_exp (v : E) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v t =
      NormedSpace.exp (t • nativeLieAdjointGenerator (I := I) (G := G) v) :=
  linearODE_eq_exp (nativeLieAdjointCurve_zero v) (nativeLieAdjointCurve_hasDerivAt v) t

 theorem nativeLieAdjoint_exponential_eq_exp (v : E) :
    nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) =
      NormedSpace.exp (nativeLieAdjointGenerator (I := I) (G := G) v) := by
  simpa only [nativeLieAdjointCurve, nativeLieExponential, one_smul]
    using nativeLieAdjointCurve_eq_exp (I := I) (G := G) v 1

 theorem nativeLieAdjointGenerator_curve_commute (v : E) (t : ℝ) :
    Commute (nativeLieAdjointGenerator (I := I) (G := G) v)
      (nativeLieAdjointCurve (I := I) (G := G) v t) := by
  letI : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)
  rw [nativeLieAdjointCurve_eq_exp]
  exact ((Commute.refl (nativeLieAdjointGenerator (I := I) (G := G) v)).smul_right t).exp_right

 theorem nativeLieAdjointCurve_hasDerivAt_left (v : E) (t : ℝ) :
    HasDerivAt (nativeLieAdjointCurve (I := I) (G := G) v)
      (nativeLieAdjointGenerator (I := I) (G := G) v * nativeLieAdjointCurve (I := I) (G := G) v t) t := by
  rw [(nativeLieAdjointGenerator_curve_commute v t).eq]
  exact nativeLieAdjointCurve_hasDerivAt v t

end Hindman168
