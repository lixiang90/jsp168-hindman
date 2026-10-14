import Hindman168.NativeLieRationalInternalLayers
import Hindman168.NativeLieRationalAffineLayer

/-! The actual original BCH error improves the internal rational
lower-central layer of the specified Q Lie subalgebra. This specializes
to W_Gamma = span_Q Log Gamma without assuming that Log Gamma is
additive, or that W_Gamma is closed in the real topology. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieLogarithmLift_rational_internal_layer
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) {u w : E} (hu : u ∈ V)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) (q : ℚ) :
    nativeLieLogarithmLift (E := E) (I := I) (G := G) w u (q : ℝ) - (u + q • w) ∈
      nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) := by
  apply nativeLieLogarithmLift_rational_sub_affine_mem V
    (nativeLieRationalInternalLayer (I := I) (G := G) V hbr j)
    (nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1))
  · exact nativeLieRationalInternalLayer_antitone V hbr (Nat.le_succ j)
  · exact nativeLieRationalInternalLayer_le V hbr j
  · exact fun _ hv _ hw => nativeLieAdjointDifferential_mem_rational V hbr hv hw
  · exact fun _ hv _ hw => nativeLieRationalInternalLayer_differential_next V hbr j hv hw
  · exact hw
  · exact hu

variable [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieGlobalLogarithm_product_internal_layer
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) {u w : E} (hu : u ∈ V)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) -
        (u + w) ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1) := by
  rw [nativeLieGlobalLogarithm_product_exponentials]
  simpa only [Rat.cast_one, one_smul] using
    nativeLieLogarithmLift_rational_internal_layer V hbr j hu hw 1

 theorem nativeLieGlobalLogarithm_product_internal_last_exact
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) (hj : j + 1 = Group.nilpotencyClass G)
    {u w : E} (hu : u ∈ V)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) =
        u + w := by
  have he := nativeLieGlobalLogarithm_product_internal_layer V hbr j hu hw
  rw [hj, nativeLieRationalInternalLayer_nilpotencyClass_bot] at he
  exact sub_eq_zero.mp he

noncomputable def nativeSubgroupRationalInternalLayer (Γ : Subgroup G) (j : ℕ) : Submodule ℚ E :=
  nativeLieRationalInternalLayer (I := I) (G := G)
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ) j

 theorem nativeSubgroupRationalInternalLayer_zero (Γ : Subgroup G) :
    nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ 0 =
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
  nativeLieRationalInternalLayer_zero _ _

 theorem nativeSubgroupRationalInternalLayer_nilpotencyClass_bot (Γ : Subgroup G) :
    nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (Group.nilpotencyClass G) = ⊥ :=
  nativeLieRationalInternalLayer_nilpotencyClass_bot _ _

 theorem nativeSubgroupRationalGlobalLogarithm_product_internal_layer
    (Γ : Subgroup G) (j : ℕ) {u w : E}
    (hu : u ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
    (hw : w ∈ nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) -
        (u + w) ∈ nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + 1) :=
  nativeLieGlobalLogarithm_product_internal_layer _ _ j hu hw

 theorem nativeSubgroupRationalGlobalLogarithm_mul_error_internal_first
    (Γ : Subgroup G) {g h : G} (hg : g ∈ Γ) (hh : h ∈ Γ) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g * h) -
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g +
        nativeLieGlobalLogarithm (E := E) (I := I) (G := G) h) ∈
      nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ 1 := by
  have hu := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg
  have hw := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hh
  rw [← nativeSubgroupRationalInternalLayer_zero (E := E) (I := I) Γ] at hw
  have hp := nativeSubgroupRationalGlobalLogarithm_product_internal_layer Γ 0 hu hw
  simpa only [nativeLieExponential_globalLogarithm] using hp

end Hindman168
