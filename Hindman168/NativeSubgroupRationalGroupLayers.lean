import Hindman168.NativeLieRationalInternalGeneration
import Hindman168.NativeSubgroupRationalNormalizedSpan

/-! The actual original lower-central series of every specified
subgroup maps, under the original global logarithm, into the INTERNAL
rational lower-central series of its own rational log span. No equality
of these two series is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff commutatorElement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeSubgroupLowerCentralSeries_le_internal_exponential
    (Γ : Subgroup G) (j : ℕ) :
    Γ.lowerCentralSeries j ≤ nativeLieRationalInternalSubgroup (I := I) (G := G)
      (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ)
      (nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ) j := by
  let V := nativeSubgroupRationalLogSpan (E := E) (I := I) Γ
  let hbr := nativeSubgroupRationalLogSpan_bracket_closed (E := E) (I := I) Γ
  induction j with
  | zero =>
    intro g hg
    apply (nativeLieRationalInternalSubgroup_mem_logarithm_iff V hbr 0 g).mpr
    rw [nativeLieRationalInternalLayer_zero]
    exact nativeSubgroup_logarithm_mem_span Γ hg
  | succ j ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro g hg h hh
    have hv := nativeSubgroup_logarithm_mem_span (E := E) (I := I) Γ hg
    have hw := (nativeLieRationalInternalSubgroup_mem_logarithm_iff V hbr j h).mp (ih hh)
    have hc := nativeLieGlobalLogarithm_commutator_mem_internal_next V hbr hv j hw
    rw [nativeLieExponential_globalLogarithm, nativeLieExponential_globalLogarithm] at hc
    exact (nativeLieRationalInternalSubgroup_mem_logarithm_iff V hbr (j + 1) ⁅g, h⁆).mpr hc

 theorem nativeSubgroupLowerCentralSeries_log_mem_internal
    (Γ : Subgroup G) (j : ℕ) {g : G} (hg : g ∈ Γ.lowerCentralSeries j) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈
      nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j :=
  (nativeLieRationalInternalSubgroup_mem_logarithm_iff _ _ j g).mp
    (nativeSubgroupLowerCentralSeries_le_internal_exponential Γ j hg)

 theorem nativeSubgroupLowerCentralSeries_rationalSpan_le_internal
    (Γ : Subgroup G) (j : ℕ) :
    nativeSubgroupRationalLogSpan (E := E) (I := I) (Γ.lowerCentralSeries j) ≤
      nativeSubgroupRationalInternalLayer (E := E) (I := I) Γ j := by
  apply Submodule.span_le.mpr
  rintro v ⟨g, hg, rfl⟩
  exact nativeSubgroupLowerCentralSeries_log_mem_internal Γ j hg

end Hindman168
