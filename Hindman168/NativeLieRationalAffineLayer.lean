import Hindman168.NativeLieRationalMixedDefect
import Hindman168.NativeLieRationalProductCurve

/-! The actual original product logarithm has its affine error in an
arbitrary specified rational layer N when brackets of V with F improve
to N. Finite rational polynomial primitives prove membership, without
treating a Q-subspace as topologically closed. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLiePicard_rational_sub_affine_mem
    (V F N : Submodule ℚ E) (hNF : N ≤ F) (hFV : F ≤ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    (hc : 0 < Group.nilpotencyClass G)
    {w u : E} (hw : w ∈ F) (hu : u ∈ V) (n : ℕ) (q : ℚ) :
    continuousPicardIterate (nativeLieLogarithmVectorField (I := I) (G := G) w) u
      (n + 1) (q : ℝ) - (u + q • w) ∈ N := by
  rw [← nativeLieRationalPicardPolynomial_eval (I := I) (G := G)]
  rw [nativeLieRationalPicardPolynomial,
    nativeLieRationalFieldPolynomial_split_zero (I := I) (G := G) hc,
    finiteVectorPolynomialPrimitive_append, finiteVectorPolynomialEval_append,
    finiteVectorPolynomialEval_append, finiteVectorPolynomialEval_singleton,
    pow_zero, one_smul, finiteVectorPolynomialEval_primitive_constant,
    Rat.cast_smul_eq_qsmul]
  have hp := nativeLieRationalPicardPolynomial_coefficients_mem V hVV (hFV hw) hu n
  have ht := nativeLieRationalFieldPolynomial_positive_tail_coefficients_mem
    V F N hNF hB hp (finiteVectorPolynomialCoefficientsMem_singleton F 0 hw)
  have hm := finiteVectorPolynomialEval_rational_mem N
    (finiteVectorPolynomialCoefficientsMem_primitive N ht) q
  convert hm using 1
  abel

include I in
omit [Module ℚ E] in
 theorem nativeLie_model_zero_of_nilpotencyClass_zero
    (hc : Group.nilpotencyClass G = 0) (v : E) : v = 0 := by
  have hb := nativeLieLowerCentralModel_nilpotencyClass_bot (I := I) (G := G)
  rw [hc, nativeLieLowerCentralModel_zero] at hb
  have hv : v ∈ (⊥ : Submodule ℝ E) := hb ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ E))
  exact hv

 theorem nativeLieLogarithmLift_rational_sub_affine_mem
    (V F N : Submodule ℚ E) (hNF : N ≤ F) (hFV : F ≤ V)
    (hVV : ∀ v ∈ V, ∀ w ∈ V, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    {w u : E} (hw : w ∈ F) (hu : u ∈ V) (q : ℚ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u (q : ℝ) - (u + q • w) ∈ N := by
  by_cases hc : Group.nilpotencyClass G = 0
  · rw [nativeLie_model_zero_of_nilpotencyClass_zero (I := I) (G := G) hc
      (nativeLieLogarithmLift (E := E) (I := I) (G := G) w u (q : ℝ) - (u + q • w))]
    exact N.zero_mem
  · exact nativeLiePicard_rational_sub_affine_mem V F N hNF hFV hVV hB
      (Nat.pos_of_ne_zero hc) hw hu (Group.nilpotencyClass G) q

variable [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieGlobalLogarithm_product_rational_layer
    (V F N : Submodule ℚ E) (hNF : N ≤ F) (hFV : F ≤ V)
    (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    {u w : E} (hu : u ∈ V) (hw : w ∈ F) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) -
        (u + w) ∈ N := by
  rw [nativeLieGlobalLogarithm_product_exponentials]
  simpa only [Rat.cast_one, one_smul] using
    nativeLieLogarithmLift_rational_sub_affine_mem V F N hNF hFV
      (fun _ hv _ hw => nativeLieAdjointDifferential_mem_rational V hbr hv hw) hB hw hu 1

end Hindman168
