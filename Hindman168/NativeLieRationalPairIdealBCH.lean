import Hindman168.RationalBilinearPairIdeal
import Hindman168.NativeLieRationalAffineLayer

/-! The genuine native BCH affine error lies in N whenever N is stable
under brackets with V and the actual bracket of the two given vectors
lies in N. The auxiliary pair span is constructed and proved closed;
no rational BCH identity or quotient logarithm is supplied. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
 theorem nativeLieAdjointDifferential_self (v : E) :
    nativeLieAdjointDifferential (I := I) (G := G) v v = 0 := by
  rw [← nativeLieAdjointGenerator_eq_differential (I := I) (G := G)]
  exact nativeLieAdjointGenerator_self (I := I) (G := G) v

omit [Module ℚ E] in
 theorem nativeLieAdjointDifferential_skew (v w : E) :
    nativeLieAdjointDifferential (I := I) (G := G) v w =
      -nativeLieAdjointDifferential (I := I) (G := G) w v := by
  rw [← nativeLieAdjointGenerator_eq_differential (I := I) (G := G),
    ← nativeLieAdjointGenerator_eq_differential (I := I) (G := G)]
  exact nativeLieAdjointGenerator_alternating (I := I) (G := G) v w

variable [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

 theorem nativeLieGlobalLogarithm_product_pair_ideal
    (V N : Submodule ℚ E) (hNV : N ≤ V)
    (hideal : ∀ v ∈ V, ∀ n ∈ N, nativeLieAdjointDifferential (I := I) (G := G) v n ∈ N)
    {u w : E} (hu : u ∈ V) (hw : w ∈ V)
    (huw : nativeLieAdjointDifferential (I := I) (G := G) u w ∈ N) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
      (nativeLieExponential (I := I) (G := G) u * nativeLieExponential (I := I) (G := G) w) -
        (u + w) ∈ N := by
  let P : Submodule ℚ E := Submodule.span ℚ ({u, w} : Set E) ⊔ N
  have hNP : N ≤ P := le_sup_right
  have huP : u ∈ P := (show Submodule.span ℚ ({u, w} : Set E) ≤ P from le_sup_left) (Submodule.subset_span (Set.mem_insert u _))
  have hwP : w ∈ P := (show Submodule.span ℚ ({u, w} : Set E) ≤ P from le_sup_left) (Submodule.subset_span (Set.mem_insert_of_mem u (Set.mem_singleton w)))
  have hPP : ∀ a ∈ P, ∀ b ∈ P,
      nativeLieAdjointDifferential (I := I) (G := G) a b ∈ N := by
    intro a ha b hb
    exact rationalBilinearPairIdeal_mem V N hNV _
      (nativeLieAdjointDifferential_self (I := I) (G := G))
      (nativeLieAdjointDifferential_skew (I := I) (G := G))
      hideal hu hw huw ha hb
  have hbrP : nativeLieRationalBracketClosed (I := I) (G := G) P := by
    intro a b ha hb
    have hm := hNP (hPP a ha b hb)
    rw [← nativeLieAdjointGenerator_eq_differential (E := E) (I := I) (G := G)] at hm
    exact (nativeLieAdjointGenerator_eq_native_bracket (I := I) (G := G) a b) ▸ hm
  exact nativeLieGlobalLogarithm_product_rational_layer P P N hNP le_rfl hbrP hPP huP hwP

end Hindman168
