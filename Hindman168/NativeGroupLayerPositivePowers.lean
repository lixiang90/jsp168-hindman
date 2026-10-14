import Hindman168.NativeLieLayerLatticeCompact
import Hindman168.NativeSubgroupRationalLayerEquality

/-! The rational saturation of each actual algebraic group layer is
exactly the corresponding original exponential Lie layer. This is a
positive-power statement, not yet equality of the layers themselves. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeSubgroupRationalLogSpan_top :
    nativeSubgroupRationalLogSpan (E := E) (I := I) (⊤ : Subgroup G) = ⊤ := by
  apply top_unique
  intro v _
  have hv := nativeSubgroup_logarithm_mem_span (E := E) (I := I) (⊤ : Subgroup G)
    (g := nativeLieExponential (I := I) (G := G) v) (Subgroup.mem_top _)
  simpa only [nativeLieGlobalLogarithm_exponential] using hv

omit [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G] in
theorem nativeLieRationalInternalLayer_top
    (hbr : nativeLieRationalBracketClosed (I := I) (G := G) (⊤ : Submodule ℚ E)) (j : ℕ) :
    nativeLieRationalInternalLayer (I := I) (G := G) ⊤ hbr j =
      (nativeLieLowerCentralModel (I := I) (G := G) j).restrictScalars ℚ := by
  let A := nativeLieRationalSubalgebra (I := I) (G := G) ⊤ hbr
  have hs : Function.Surjective A.incl := fun x => ⟨⟨x, trivial⟩, rfl⟩
  have he := hs.lieModule_lcs_map_eq (g := A.incl.toLinearMap) (fun _ _ => rfl) hs j
  change (LieModule.lowerCentralSeries ℚ A A j).toSubmodule.map A.incl.toLinearMap = _
  rw [he]
  apply SetLike.coe_injective
  exact (LieModule.coe_lowerCentralSeries_eq_int ℚ (GroupLieAlgebra I G)
    (GroupLieAlgebra I G) j).trans
      (LieModule.coe_lowerCentralSeries_eq_int ℝ (GroupLieAlgebra I G)
        (GroupLieAlgebra I G) j).symm

theorem nativeGroupLowerCentralSeries_rationalLogSpan_eq (j : ℕ) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) ((⊤ : Subgroup G).lowerCentralSeries j) =
      (nativeLieLowerCentralModel (I := I) (G := G) j).restrictScalars ℚ := by
  rw [nativeSubgroupLowerCentralSeries_rationalSpan_eq_internal]
  unfold nativeSubgroupRationalInternalLayer
  have h : ∀ (V : Submodule ℚ E)
      (hb : nativeLieRationalBracketClosed (I := I) (G := G) V), V = ⊤ →
        nativeLieRationalInternalLayer (I := I) (G := G) V hb j =
          (nativeLieLowerCentralModel (I := I) (G := G) j).restrictScalars ℚ := by
    intro V hb hV
    subst V
    exact nativeLieRationalInternalLayer_top _ j
  exact h _ _ (nativeSubgroupRationalLogSpan_top (E := E) (I := I) (G := G))

theorem nativeLieLowerCentralSubgroup_mem_iff_positive_power (j : ℕ) (g : G) :
    g ∈ nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j ↔
      ∃ n : ℕ, 0 < n ∧ g ^ n ∈ (⊤ : Subgroup G).lowerCentralSeries j := by
  have he := nativeSubgroupRationalLogSpan_mem_iff_positive_power (E := E) (I := I)
    ((⊤ : Subgroup G).lowerCentralSeries j)
    (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
  rw [nativeGroupLowerCentralSeries_rationalLogSpan_eq,
    nativeLieExponential_globalLogarithm] at he
  exact (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E)
    (LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
      (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j)) g).trans he

end Hindman168
