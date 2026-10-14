import Hindman168.NativeLieRationalInternalLayers
import Hindman168.NativeLieAdjointLayer
import Hindman168.NativeLieAdjointNatPolynomial

/-! Actual adjoint action and its first bracket term in the INTERNAL
rational lower-central series. Rational factorial coefficients make
both remainders actual members of the original rational layers. -/

namespace Hindman168
open Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

omit [Group.IsNilpotent G] in
 theorem nativeLieAdjointGenerator_pow_mem_internal
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) (n : ℕ) :
    (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + n) := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, Nat.add_zero] using hw
  | succ n ih =>
    rw [pow_succ']
    have he := nativeLieRationalInternalLayer_differential_next V hbr (j + n) hv ih
    rw [← nativeLieAdjointGenerator_eq_differential (I := I) (G := G) v] at he
    exact he

 theorem nativeLieAdjoint_exponential_sub_mem_internal_next
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w - w ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) := by
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v)
  change A w - w ∈ _
  have ha : A w - w = (A - 1) w := by simp only [sub_apply, one_apply_eq_self]
  rw [ha, nativeLieAdjoint_exponential_sub_one_finite_formula]
  simp only [_root_.sum_apply, smul_apply]
  apply Submodule.sum_mem
  intro n _
  have hc : ((((n + 1).factorial : ℚ)⁻¹ : ℚ) : ℝ) = ((n + 1).factorial : ℝ)⁻¹ := by push_cast; rfl
  rw [← hc, Rat.cast_smul_eq_qsmul]
  apply Submodule.smul_mem
  exact nativeLieRationalInternalLayer_antitone V hbr (by omega)
    (nativeLieAdjointGenerator_pow_mem_internal V hbr hv j hw (n + 1))

 theorem nativeLieAdjoint_exponential_sub_generator_rational_formula (v w : E) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w - w -
      nativeLieAdjointGenerator (I := I) (G := G) v w =
    ∑ n ∈ range (Group.nilpotencyClass G), ((n + 2).factorial : ℚ)⁻¹ •
      (nativeLieAdjointGenerator (I := I) (G := G) v ^ (n + 2)) w := by
  have hf := nativeLieAdjointCurve_apply_padded_rational_polynomial (I := I) (G := G) v w 1
  simp only [one_pow, one_smul] at hf
  change (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w =
    ∑ n ∈ range (Group.nilpotencyClass G + 1 + 1),
      ((n.factorial : ℚ)⁻¹) • (nativeLieAdjointGenerator (I := I) (G := G) v ^ n) w at hf
  rw [sum_range_succ', sum_range_succ'] at hf
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    pow_zero, one_apply_eq_self, pow_one, one_smul, Nat.zero_add] at hf
  rw [hf]
  abel

 theorem nativeLieAdjoint_exponential_sub_generator_mem_internal_two
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w - w -
      nativeLieAdjointDifferential (I := I) (G := G) v w ∈
        nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2) := by
  rw [← nativeLieAdjointGenerator_eq_differential (I := I) (G := G),
    nativeLieAdjoint_exponential_sub_generator_rational_formula]
  apply Submodule.sum_mem
  intro n _
  apply Submodule.smul_mem
  exact nativeLieRationalInternalLayer_antitone V hbr (by omega)
    (nativeLieAdjointGenerator_pow_mem_internal V hbr hv j hw (n + 2))

 theorem nativeLieAdjoint_exponential_mem_internal
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    (nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr j := by
  have hd := nativeLieAdjoint_exponential_sub_mem_internal_next V hbr hv j hw
  have hm := (nativeLieRationalInternalLayer (I := I) (G := G) V hbr j).add_mem
    (nativeLieRationalInternalLayer_antitone V hbr (Nat.le_succ j) hd) hw
  simpa only [sub_add_cancel] using hm

end Hindman168
