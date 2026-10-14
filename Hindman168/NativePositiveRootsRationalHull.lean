import Hindman168.PositiveSubgroupRoots
import Hindman168.NativeSubgroupRationalHull
import Hindman168.NativeLiePowerRoots

/-! Positive-power membership implies membership in the actual original
rational logarithmic hull. The hull itself is closed under positive
roots by real/rational scalar compatibility and actual Log(g^n).
This does not assume or prove general multiplication closure of roots
of the actual specified subgroup. -/

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem nativeLie_logarithm_mem_rational_of_positive_power (V : Submodule ℚ E)
    (g : G) {n : ℕ} (hn : 0 < n)
    (h : nativeLieGlobalLogarithm (E := E) (I := I) (G := G) (g ^ n) ∈ V) :
    nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g ∈ V := by
  rw [nativeLieGlobalLogarithm_pow] at h
  rw [Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℚ] at h
  exact (smul_mem_iff V (show (n : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))).mp h

theorem positiveSubgroupRoots_le_nativeRationalHull (Γ : Subgroup G) :
    positiveSubgroupRoots Γ ⊆ (nativeSubgroupRationalHull (E := E) (I := I) Γ : Set G) := by
  rintro g ⟨n, hn, hgn⟩
  apply (nativeSubgroupRationalHull_mem_iff Γ g).mpr
  exact nativeLie_logarithm_mem_rational_of_positive_power _ g hn
    (nativeSubgroup_logarithm_mem_span Γ hgn)

theorem nativeSubgroupRationalHull_positive_root (Γ : Subgroup G) {g : G} {n : ℕ}
    (hn : 0 < n) (hg : g ^ n ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ) :
    g ∈ nativeSubgroupRationalHull (E := E) (I := I) Γ :=
  (nativeSubgroupRationalHull_mem_iff Γ g).mpr
    (nativeLie_logarithm_mem_rational_of_positive_power _ g hn
      ((nativeSubgroupRationalHull_mem_iff Γ (g ^ n)).mp hg))

theorem nativeSubgroupRationalHull_logarithm_span_eq (Γ : Subgroup G) :
    nativeSubgroupRationalLogSpan (E := E) (I := I)
      (nativeSubgroupRationalHull (E := E) (I := I) Γ) =
      nativeSubgroupRationalLogSpan (E := E) (I := I) Γ := by
  apply le_antisymm
  · exact nativeSubgroupRationalLogSpan_le_of_logarithms_mem _ _
      (fun g hg => (nativeSubgroupRationalHull_mem_iff Γ g).mp hg)
  · apply span_mono
    exact image_mono (nativeSubgroup_le_rationalHull (E := E) (I := I) Γ)

end Hindman168
