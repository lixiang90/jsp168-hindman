import Hindman168.NativeLieRationalPicardPolynomial

/-! Rational BCH closure in the original arbitrary nilpotent Lie group.
The rational structure is an actual Q-linear subspace closed under the
original native bracket. Explicit polynomial Picard curves prove rational
product logarithms and the exponential image subgroup law. No closedness
of this Q-subspace, additive lattice logarithms or cocompactness is assumed. -/

namespace Hindman168
open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

def nativeLieRationalBracketClosed (V : Submodule ℚ E) : Prop :=
  ∀ x y : GroupLieAlgebra I G, (x : E) ∈ V → (y : E) ∈ V →
    ((⁅x, y⁆ : GroupLieAlgebra I G) : E) ∈ V

omit [Group.IsNilpotent G] in
 theorem nativeLieAdjointDifferential_mem_rational
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {v w : E} (hv : v ∈ V) (hw : w ∈ V) :
    nativeLieAdjointDifferential (I := I) (G := G) v w ∈ V := by
  let x : GroupLieAlgebra I G := v
  let y : GroupLieAlgebra I G := w
  have h : (⁅x, y⁆ : GroupLieAlgebra I G) ∈ V := hbr x y hv hw
  have hc : nativeLieAdjointGenerator (I := I) (G := G) v w ∈ V :=
    (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) x y).symm ▸ h
  rw [nativeLieAdjointGenerator_eq_differential] at hc
  exact hc

 theorem nativeLieLogarithmLift_mem_rational_structure
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {w u : E} (hw : w ∈ V) (hu : u ∈ V) (q : ℚ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u (q : ℝ) ∈ V :=
  nativeLieLogarithmLift_rational_mem V
    (fun _ hv _ hw => nativeLieAdjointDifferential_mem_rational V hbr hv hw) hw hu q

variable [FiniteDimensional ℝ E]

noncomputable def nativeLieRationalExponentialSubgroup
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) : Subgroup G where
  carrier := (fun v : E => nativeLieExponential (I := I) (G := G) v) '' (V : Set E)
  one_mem' := ⟨0, V.zero_mem, nativeLieExponential_zero (I := I) (G := G)⟩
  mul_mem' := by
    rintro a b ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    refine ⟨nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1, ?_,
      nativeLieExponential_product_logarithm (E := E) (I := I) (G := G) u w⟩
    change nativeLieLogarithmLift (E := E) (I := I) (G := G) w u 1 ∈ V
    simpa only [Rat.cast_one] using
      nativeLieLogarithmLift_mem_rational_structure (E := E) V hbr hw hu (1 : ℚ)
  inv_mem' := by
    rintro a ⟨u, hu, rfl⟩
    exact ⟨-u, V.neg_mem hu, nativeLieExponential_neg (I := I) (G := G) u⟩

variable [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieRationalBCH_mem
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) ∈ V := by
  rw [nativeLieGlobalLogarithm_product_exponentials]
  simpa only [Rat.cast_one] using nativeLieLogarithmLift_mem_rational_structure V hbr hw hu (1 : ℚ)

 theorem nativeLieRationalExponentialSubgroup_mem_logarithm_iff
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V) (g : G) :
    g ∈ nativeLieRationalExponentialSubgroup (I := I) (G := G) V hbr ↔
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V := by
  let exp : E → G := fun v => nativeLieExponential (I := I) (G := G) v
  let log : G → E := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  constructor
  · rintro ⟨v, hv, rfl⟩
    change log (exp v) ∈ V
    have he : log (exp v) = v := nativeLieGlobalLogarithm_exponential (E := E) (I := I) (G := G) v
    rw [he]
    exact hv
  · intro hg
    exact ⟨log g, hg, nativeLieExponential_globalLogarithm (E := E) (I := I) (G := G) g⟩

end Hindman168
