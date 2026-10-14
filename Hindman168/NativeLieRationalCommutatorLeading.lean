import Hindman168.NativeLieRationalPairIdealBCH
import Hindman168.NativeLieRationalAdjointInternal

/-! The logarithm of an actual original group commutator equals the
actual original native Lie bracket modulo the next internal rational
layer. Conjugation, inverse exponentials and both genuine rational
remainders are retained explicitly. -/

namespace Hindman168
open scoped Manifold ContDiff commutatorElement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

omit [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
 theorem nativeLieRationalInternalLayer_ideal
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) {v n : E} (hv : v ∈ V)
    (hn : n ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieAdjointDifferential (I := I) (G := G) v n ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr j :=
  nativeLieRationalInternalLayer_antitone V hbr (Nat.le_succ j)
    (nativeLieRationalInternalLayer_differential_next V hbr j hv hn)

 theorem nativeLieGlobalLogarithm_commutator_sub_adjoint_internal_two
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      ⁅nativeLieExponential (I := I) (G := G) v, nativeLieExponential (I := I) (G := G) w⁆ -
        ((nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) : E →L[ℝ] E) w - w) ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2) := by
  let exp : E → G := fun a => nativeLieExponential (I := I) (G := G) a
  let B := nativeLieAdjointDifferential (I := I) (G := G)
  let A : E →L[ℝ] E := nativeLieAdjoint (I := I) (exp v)
  let N := nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2)
  have hwV := nativeLieRationalInternalLayer_le V hbr j hw
  have hAwV := nativeLieRationalInternalLayer_le V hbr j
    (nativeLieAdjoint_exponential_mem_internal V hbr hv j hw)
  have hd := nativeLieAdjoint_exponential_sub_mem_internal_next V hbr hv j hw
  have hb : B (A w) (-w) ∈ N := by
    have he : B (A w) (-w) = B w (A w - w) := by
      change nativeLieAdjointDifferential (I := I) (G := G) (A w) (-w) =
        nativeLieAdjointDifferential (I := I) (G := G) w (A w - w)
      simp only [map_neg, map_sub, nativeLieAdjointDifferential_self, sub_zero]
      rw [nativeLieAdjointDifferential_skew]
      simp only [neg_neg]
    rw [he]
    exact nativeLieRationalInternalLayer_differential_next V hbr (j + 1) hwV hd
  have hp := nativeLieGlobalLogarithm_product_pair_ideal V N
    (nativeLieRationalInternalLayer_le V hbr (j + 2))
    (fun _ ha _ hn => nativeLieRationalInternalLayer_ideal V hbr (j + 2) ha hn)
    hAwV (V.neg_mem hwV) hb
  have hc : exp v * exp w * (exp v)⁻¹ = exp (A w) :=
    nativeLieAdjoint_exponential_conjugation (I := I) (exp v) w
  have hi : exp (-w) = (exp w)⁻¹ := nativeLieExponential_neg (I := I) (G := G) w
  change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) ⁅exp v, exp w⁆ - (A w - w) ∈ N
  rw [commutatorElement_def, hc, ← hi]
  simpa only [sub_eq_add_neg] using hp

 theorem nativeLieGlobalLogarithm_commutator_leading_internal
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      ⁅nativeLieExponential (I := I) (G := G) v, nativeLieExponential (I := I) (G := G) w⁆ -
        nativeLieAdjointDifferential (I := I) (G := G) v w ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2) := by
  have hp := nativeLieGlobalLogarithm_commutator_sub_adjoint_internal_two V hbr hv j hw
  have ha := nativeLieAdjoint_exponential_sub_generator_mem_internal_two V hbr hv j hw
  have hm := (nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 2)).add_mem hp ha
  convert hm using 1
  abel

 theorem nativeLieGlobalLogarithm_commutator_mem_internal_next
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (j : ℕ)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      ⁅nativeLieExponential (I := I) (G := G) v, nativeLieExponential (I := I) (G := G) w⁆ ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) := by
  have hp := nativeLieGlobalLogarithm_commutator_leading_internal V hbr hv j hw
  have hb := nativeLieRationalInternalLayer_differential_next V hbr j hv hw
  have hm := (nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1)).add_mem
    (nativeLieRationalInternalLayer_antitone V hbr (by omega) hp) hb
  simpa only [sub_add_cancel] using hm

end Hindman168
