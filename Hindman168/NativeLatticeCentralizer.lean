import Hindman168.NativeLieExponentialCommuteIff
import Hindman168.NativeLatticeRealSpanning
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The centralizer of an actual cocompact subgroup is the center of
the original simply connected nilpotent Lie group. The actual logarithms
span the original real model; the true adjoint generator kernel contains
these logarithms and therefore is the whole model. -/

namespace Hindman168
open Function Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_mem_center_iff_generator_eq_zero (v : E) :
    nativeLieExponential (I := I) (G := G) v ∈ Subgroup.center G ↔
    nativeLieAdjointGenerator (I := I) (G := G) v = 0 := by
  constructor
  · intro h
    ext w
    have hc : Commute (nativeLieExponential (I := I) (G := G) v)
        (nativeLieExponential (I := I) (G := G) w) :=
      (Subgroup.mem_center_iff.mp h _).symm
    exact nativeLieAdjointGenerator_apply_eq_zero_of_exponentials_commute hc
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro g
    have hc := nativeLieCurves_commute_of_generator_apply_eq_zero
      (I := I) (G := G) (v := v)
      (w := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
      (by rw [h]; rfl) 1 1
    change nativeLieExponential (I := I) (G := G) v *
      nativeLieExponential (I := I) (G := G)
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) =
      nativeLieExponential (I := I) (G := G)
        (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) *
      nativeLieExponential (I := I) (G := G) v at hc
    rw [nativeLieExponential_globalLogarithm] at hc
    exact hc.symm

 theorem nativeLie_mem_center_iff_logarithm_generator_eq_zero (g : G) :
    g ∈ Subgroup.center G ↔ nativeLieAdjointGenerator (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g) = 0 := by
  simpa only [nativeLieExponential_globalLogarithm] using
    nativeLieExponential_mem_center_iff_generator_eq_zero
      (I := I) (G := G) (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)

variable [Module ℚ E]

include I

 theorem nativeLattice_centralizer_eq_center (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    Subgroup.centralizer (Γ : Set G) = Subgroup.center G := by
  apply le_antisymm
  · intro g hg
    apply (nativeLie_mem_center_iff_logarithm_generator_eq_zero (E := E) (I := I) g).mpr
    let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g)
    have hspan : span ℝ ((nativeLieGlobalLogarithm (E := E) (I := I) (G := G)) ''
        (Γ : Set G)) ≤ B.ker := by
      apply span_le.mpr
      rintro w ⟨γ, hγ, rfl⟩
      have hc : Commute (nativeLieExponential (I := I) (G := G)
          (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g))
          (nativeLieExponential (I := I) (G := G)
            (nativeLieGlobalLogarithm (E := E) (I := I) (G := G) γ)) := by
        rw [nativeLieExponential_globalLogarithm, nativeLieExponential_globalLogarithm]
        exact (Subgroup.mem_centralizer_iff.mp hg γ hγ).symm
      exact nativeLieAdjointGenerator_apply_eq_zero_of_exponentials_commute hc
    rw [nativeSubgroup_logarithms_real_span_eq_top (E := E) (I := I) Γ] at hspan
    ext w
    exact hspan mem_top
  · exact Subgroup.center_le_centralizer _

end Hindman168
