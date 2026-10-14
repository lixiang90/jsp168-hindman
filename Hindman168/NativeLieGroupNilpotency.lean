import Hindman168.NativeLieCommutatorProducts
import Hindman168.LieLowerCentralProductCutoff

/-! Original group nilpotency implies original native Lie-algebra
nilpotency with the same lower-central cutoff. This follows from actual
group commutator derivatives and the original native Lie action, and
removes the separate Lie-nilpotency premise for the finite adjoint formula.
No equality of group/Lie lower-central layers or global inverse is asserted. -/

namespace Hindman168
open Function Set Topology Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointGenerator_products_toEnd (vs : List (GroupLieAlgebra I G)) :
    ((vs.map (nativeLieAdjointGenerator (I := I) (G := G))).prod).toLinearMap =
      (vs.map (LieModule.toEnd ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G))).prod := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons]
    calc
      _ = (nativeLieAdjointGenerator (I := I) (G := G) v).toLinearMap *
          ((vs.map (nativeLieAdjointGenerator (I := I) (G := G))).prod).toLinearMap :=
        map_mul ContinuousLinearMap.toLinearMapRingHom _ _
      _ = _ := by
        rw [nativeLieAdjointGenerator_toEnd, ih]
        rfl

 theorem nativeLieLowerCentral_bot_of_group_lowerCentral_bot {k : ℕ}
    (hk : (⊤ : Subgroup G).lowerCentralSeries k = ⊥) :
    LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) k = ⊥ := by
  apply lie_lowerCentral_eq_bot_of_action_products_zero
  intro vs hlen
  rw [← nativeLieAdjointGenerator_products_toEnd]
  have h := nativeLieAdjointGenerator_products_zero_of_lowerCentral_bot (I := I) hk vs hlen
  rw [h]
  rfl

 theorem nativeLieLowerCentral_nilpotencyClass_bot [Group.IsNilpotent G] :
    LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G)
      (Group.nilpotencyClass G) = ⊥ :=
  nativeLieLowerCentral_bot_of_group_lowerCentral_bot (I := I)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G))

 theorem nativeLieAlgebra_isNilpotent_of_group_isNilpotent [Group.IsNilpotent G] :
    LieModule.IsNilpotent (GroupLieAlgebra I G) (GroupLieAlgebra I G) :=
  LieModule.IsNilpotent.mk (M := GroupLieAlgebra I G)
    (nativeLieLowerCentral_nilpotencyClass_bot (I := I) (G := G))

 theorem nativeLieAdjointGenerator_pow_nilpotencyClass [Group.IsNilpotent G] (v : E) :
    nativeLieAdjointGenerator (I := I) (G := G) v ^ Group.nilpotencyClass G = 0 :=
  nativeLieAdjointGenerator_pow_zero_of_lowerCentral_bot (I := I)
    (Subgroup.lowerCentralSeries_nilpotencyClass (G := G)) v

 theorem nativeLieAdjointCurve_finite_formula_of_group_isNilpotent
    [Group.IsNilpotent G] (v : E) (t : ℝ) :
    nativeLieAdjointCurve (I := I) (G := G) v t =
      ∑ j ∈ Finset.range (Group.nilpotencyClass G), (j.factorial : ℝ)⁻¹ •
        ((t • nativeLieAdjointGenerator (I := I) (G := G) v) ^ j) :=
  nativeLieAdjointCurve_eq_finite_sum v (nativeLieAdjointGenerator_pow_nilpotencyClass v) t

 theorem nativeLieAdjoint_exponential_finite_formula_of_group_isNilpotent
    [Group.IsNilpotent G] (v : E) :
    nativeLieAdjoint (I := I) (nativeLieExponential (I := I) (G := G) v) =
      ∑ j ∈ Finset.range (Group.nilpotencyClass G), (j.factorial : ℝ)⁻¹ •
        (nativeLieAdjointGenerator (I := I) (G := G) v ^ j) :=
  nativeLieAdjoint_exponential_eq_finite_sum v (nativeLieAdjointGenerator_pow_nilpotencyClass v)

end Hindman168
