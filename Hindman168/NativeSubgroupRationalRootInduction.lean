import Hindman168.NativeLieRationalRootLayerSubmodule
import Hindman168.NativeSubgroupRationalLayerEquality
import Hindman168.NativeSubgroupRationalHull

/-! Terminating downward induction in the internal rational Lie layers
of the ORIGINAL specified subgroup. Their already proved equality with
its actual group-layer logarithmic spans supplies the generators.
No normality, finite generation, discreteness or lattice substitution
is required. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroup_internal_exponentials_mem_root_closed_of_terminating
    (Γ K : Subgroup G) (hΓK : Γ ≤ K)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K)
    (j n : ℕ)
    (hbot : nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ (j + n) = ⊥) :
    ∀ v ∈ nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j,
      nativeLieExponential (I := I) (G := G) v ∈ K := by
  induction n generalizing j with
  | zero =>
    intro v hv
    rw [Nat.add_zero] at hbot
    rw [hbot] at hv
    have hv0 : v = 0 := hv
    exact hv0.symm ▸ (nativeLieExponential_zero (I := I) (G := G)).symm ▸ K.one_mem
  | succ n ih =>
    have hnext := ih (j + 1) (by simpa only [Nat.add_assoc, Nat.add_comm n 1] using hbot)
    let V := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
    let hbr := nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ
    let P := nativeLieRationalRootLayerSubmodule V hbr j K hroot hnext
    have hspan : nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j) ≤ P := by
      apply nativeSubgroupRationalLogSpan_le_of_logarithms_mem
      intro g hg
      change nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
        nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j ∧
          nativeLieExponential (I := I) (G := G)
            (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) ∈ K
      refine ⟨nativeSubgroupLowerCentralSeries_log_mem_internal Γ j hg, ?_⟩
      rw [nativeLieExponential_globalLogarithm]
      exact hΓK (Γ.lowerCentralSeries_le_self j hg)
    rw [nativeSubgroupLowerCentralSeries_rationalSpan_eq_internal] at hspan
    intro v hv
    exact (hspan hv).2

 theorem nativeSubgroupRationalLogSpan_exponential_mem_root_closed
    (Γ K : Subgroup G) (hΓK : Γ ≤ K)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K)
    {v : E} (hv : v ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ) :
    nativeLieExponential (I := I) (G := G) v ∈ K := by
  apply nativeSubgroup_internal_exponentials_mem_root_closed_of_terminating
    Γ K hΓK hroot 0 (Group.nilpotencyClass G)
  · simpa only [Nat.zero_add] using
      nativeSubgroupRationalInternalLayer_nilpotencyClass_bot (E := E) (I := I) Γ
  · simpa only [nativeSubgroupRationalInternalLayer_zero] using hv

 theorem nativeSubgroupRationalHull_le_root_closed
    (Γ K : Subgroup G) (hΓK : Γ ≤ K)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K) :
    nativeSubgroupRationalHull (E := E) (I := I) Γ ≤ K := by
  intro g hg
  have hv := (nativeSubgroupRationalHull_mem_iff Γ g).mp hg
  have he := nativeSubgroupRationalLogSpan_exponential_mem_root_closed Γ K hΓK hroot hv
  simpa only [nativeLieExponential_globalLogarithm] using he

end Hindman168
