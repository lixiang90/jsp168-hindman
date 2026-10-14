import Hindman168.NativeGroupLayerPositivePowers
import Hindman168.BaireSubgroupCover
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Exact original group/Lie lower-central equality. Algebraic group
layers are sigma compact. Their positive roots cover the exponential
Lie layer through countably many genuine root homeomorphisms. Baire
category makes the original group layer open; connectedness makes it all. -/

namespace Hindman168
open Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieSubalgebraRootHomeomorph
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (n : ℕ) :
    nativeLieSubalgebraSubgroup (E := E) S ≃ₜ nativeLieSubalgebraSubgroup (E := E) S :=
  let h := nativeLieSubalgebraExponentialHomeomorph (E := E) S
  let a : ℝ := ((n + 1 : ℕ) : ℝ)⁻¹
  let d := (LinearEquiv.smulOfNeZero ℝ (nativeLieSubalgebraModel (E := E) S) a
    (inv_ne_zero (by positivity))).toContinuousLinearEquiv.toHomeomorph
  h.symm.trans (d.trans h)

omit [Module ℚ E] in
theorem nativeLieSubalgebraRootHomeomorph_pow
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G)) (n : ℕ)
    (g : nativeLieSubalgebraSubgroup (E := E) S) :
    nativeLieSubalgebraRootHomeomorph S n (g ^ (n + 1)) = g := by
  apply Subtype.ext
  let v := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g.val
  have hp : nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g.val ^ (n + 1)) =
      ((n + 1 : ℕ) : ℝ) • v := by
    have he := nativeLieExponential_nat_smul (I := I) (G := G) v (n + 1)
    have hv : nativeLieExponential (I := I) (G := G) v = g.val :=
      nativeLieExponential_globalLogarithm (I := I) g.val
    rw [hv] at he
    have hl := congrArg (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) he
    rw [nativeLieGlobalLogarithm_exponential] at hl
    exact hl.symm
  change nativeLieExponential (I := I) (G := G)
    (((n + 1 : ℕ) : ℝ)⁻¹ •
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g.val ^ (n + 1))) = g.val
  rw [hp, smul_smul, inv_mul_cancel₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), one_smul]
  exact nativeLieExponential_globalLogarithm (I := I) g.val

theorem nativeGroupLowerCentralSeries_eq_exponential (j : ℕ) :
    (⊤ : Subgroup G).lowerCentralSeries j =
      nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I (minSmoothness ℝ 3)
  let S := LieIdeal.toLieSubalgebra ℝ (GroupLieAlgebra I G)
    (LieModule.lowerCentralSeries ℝ (GroupLieAlgebra I G) (GroupLieAlgebra I G) j)
  let L := nativeLieLowerCentralSubgroup (E := E) (I := I) (G := G) j
  let A := (⊤ : Subgroup G).lowerCentralSeries j
  have hAL : A ≤ L := nativeGroupLowerCentralSeries_le_exponential j
  let K := A.comap L.subtype
  let h := nativeLieSubalgebraExponentialHomeomorph (E := E) S
  letI : BaireSpace L := h.baireSpace
  letI : ConnectedSpace L := nativeLieSubalgebraSubgroup_connected S
  have hG : IsSigmaCompact (univ : Set G) := by
    letI : SigmaCompactSpace E := ⟨⟨fun n => Metric.closedBall (0 : E) n,
      fun n => isCompact_closedBall (0 : E) n, Metric.iUnion_closedBall_nat (0 : E)⟩⟩
    have he : range (fun v : E => nativeLieExponential (I := I) (G := G) v) = univ :=
      Set.range_eq_univ.mpr (nativeLieExponential_surjective (I := I) (G := G))
    rw [← he]
    exact isSigmaCompact_range (f := fun v : E => nativeLieExponential (I := I) (G := G) v)
      (nativeLieExponential_continuous (I := I) (G := G))
  have hA : IsSigmaCompact (A : Set G) := sigmaCompact_subgroup_lowerCentralSeries ⊤ hG j
  have hK : IsSigmaCompact (K : Set L) := by
    apply IsEmbedding.subtypeVal.isSigmaCompact_iff.mpr
    have he : ((↑) : L → G) '' (K : Set L) = (A : Set G) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hg
        exact ⟨⟨g, hAL hg⟩, hg, rfl⟩
    rw [he]
    exact hA
  have htop : K = ⊤ := by
    apply sigmaCompact_subgroup_eq_top_of_homeomorph_cover K hK
      (fun n => nativeLieSubalgebraRootHomeomorph S n)
    intro x
    obtain ⟨m, hm, hxm⟩ :=
      (nativeLieLowerCentralSubgroup_mem_iff_positive_power (E := E) (I := I) j x.val).mp x.property
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact ⟨n, x ^ (n + 1), hxm, nativeLieSubalgebraRootHomeomorph_pow S n x⟩
  apply le_antisymm hAL
  intro g hg
  have hk : (⟨g, hg⟩ : L) ∈ K := htop ▸ Subgroup.mem_top _
  exact hk

include I in
theorem nativeGroupLowerCentralSeries_isClosed (j : ℕ) :
    IsClosed ((⊤ : Subgroup G).lowerCentralSeries j : Set G) := by
  rw [nativeGroupLowerCentralSeries_eq_exponential (E := E) (I := I)]
  exact nativeLieLowerCentralSubgroup_closed j

end Hindman168
