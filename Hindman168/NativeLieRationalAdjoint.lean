import Hindman168.NativeLieRationalBCH

/-! Conjugation by an original exponential with rational logarithm
preserves the actual original rational Lie structure. The actual finite
adjoint formula uses rational factorial coefficients and the original
native bracket, rather than assumed rational matrix coordinates. -/

namespace Hindman168
open Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

omit [Group.IsNilpotent G] in
 theorem nativeLieAdjointGenerator_pow_mem_rational
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈ V := by
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  change (B ^ n) w ∈ V
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hw
  | succ n ih =>
    rw [pow_succ']
    change nativeLieAdjointGenerator (I := I) (G := G) v ((B ^ n) w) ∈ V
    rw [nativeLieAdjointGenerator_eq_differential]
    exact nativeLieAdjointDifferential_mem_rational V hbr hv ih

 theorem nativeLieAdjoint_exponential_mem_rational
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w ∈ V := by
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v)
  have he : A = ∑ n ∈ range (Group.nilpotencyClass G),
      (n.factorial : ℝ)⁻¹ • nativeLieAdjointGenerator (I := I) (G := G) v ^ n :=
    nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent v
  change A w ∈ V
  rw [he]
  simp only [_root_.sum_apply, smul_apply]
  apply V.sum_mem
  intro n _
  have hc : (((n.factorial : ℚ)⁻¹ : ℚ) : ℝ) = (n.factorial : ℝ)⁻¹ := by push_cast; rfl
  rw [← hc, Rat.cast_smul_eq_qsmul]
  exact V.smul_mem _ (nativeLieAdjointGenerator_pow_mem_rational V hbr hv hw n)

variable [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieAdjoint_mem_rational_of_logarithm
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (g : G) (hg : nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V)
    {w : E} (hw : w ∈ V) : (nativeLieAdjoint (I := I) g : E →L[ℝ] E) w ∈ V := by
  let v : E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  have he : exp v = g := nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g
  have ha : (nativeLieAdjoint (I := I) (exp v) : E →L[ℝ] E) w ∈ V :=
    nativeLieAdjoint_exponential_mem_rational V hbr hg hw
  rw [he] at ha
  exact ha

end Hindman168
