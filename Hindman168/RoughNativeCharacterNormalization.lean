import Hindman168.NativeRationalCharacterKernel
import Hindman168.NativeLieRationalPowerMembership

namespace Hindman168
open Set Submodule
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_character_rational_on_span (Γ : Subgroup G) (F : E →ₗ[ℝ] ℝ)
    (hΓ : ∀ g ∈ Γ, ∃ r : ℚ, nativeLieLogarithmCharacter (I := I) (G := G) F g = (r : ℝ)) :
    ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hΓ g hg
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨s, hs⟩ := hy
    exact ⟨r + s, by rw [map_add, hr, hs, Rat.cast_add]⟩
  | smul r x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨r * s, ?_⟩
    rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, hs, Rat.cast_mul]
    rfl

theorem rough_native_integral_character_rational_on_span (Γ : Subgroup G) (F : E →ₗ[ℝ] ℝ)
    (hΓ : ∀ g ∈ Γ, ∃ n : ℤ, nativeLieLogarithmCharacter (I := I) (G := G) F g = (n : ℝ)) :
    ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ) := by
  apply rough_native_character_rational_on_span Γ F
  intro g hg
  obtain ⟨n, hn⟩ := hΓ g hg
  exact ⟨(n : ℚ), by simpa only [Rat.cast_intCast] using hn⟩

theorem rough_native_fixed_character_normalization (Γ : Subgroup G)
    (S : LieSubalgebra ℝ (GroupLieAlgebra I G))
    (hS : nativeLatticeRationalSubspace (E := E) (I := I) Γ (nativeLieSubalgebraModel S))
    (F : E →ₗ[ℝ] ℝ)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ, ∃ r : ℚ, F x = (r : ℝ))
    {v : E} (hv : v ∈ nativeLieSubalgebraModel S) (hFv : F v ≠ 0) :
    ∃ V : E, V ∈ nativeLieSubalgebraModel S ∧
      V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ ∧ F V = 1 ∧
      ∃ K : ℕ, 0 < K ∧ nativeLieExponential (I := I) (G := G) ((K : ℝ) • V) ∈ Γ := by
  obtain ⟨g, hg, hgS, hgF⟩ := nativeRationalLieSubalgebra_exists_actual_lattice_pivot Γ S hS F hv hFv
  let u := nativeLieGlobalLogarithm (E := E) (I := I) (G := G) g
  have huS : u ∈ nativeLieSubalgebraModel S :=
    (nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff (E := E) S g).mp hgS
  have huQ : u ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    nativeSubgroup_logarithm_mem_span Γ hg
  obtain ⟨r, hr⟩ := hQ u huQ
  have hr0 : r ≠ 0 := by
    intro hz
    apply hgF
    change F u = 0
    rw [hr, hz, Rat.cast_zero]
  let V : E := r⁻¹ • u
  have hVS : V ∈ nativeLieSubalgebraModel S := by
    dsimp [V]
    rw [← Rat.cast_smul_eq_qsmul ℝ]
    exact (nativeLieSubalgebraModel S).smul_mem _ huS
  have hVQ : V ∈ nativeSubgroupRationalLogSpan (E := E) (I := I) Γ :=
    (nativeSubgroupRationalLogSpan (E := E) (I := I) Γ).smul_mem r⁻¹ huQ
  have hFV : F V = 1 := by
    dsimp [V]
    rw [← Rat.cast_smul_eq_qsmul ℝ, map_smul, hr, Rat.cast_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hr0)
  refine ⟨V, hVS, hVQ, hFV, r⁻¹.den, r⁻¹.den_pos, ?_⟩
  rw [nativeLieExponential_nat_smul]
  change nativeLieExponential (I := I) (G := G) (r⁻¹ • u) ^ r⁻¹.den ∈ Γ
  rw [nativeLieExponential_rat_power_den, nativeLieExponential_globalLogarithm]
  exact Γ.zpow_mem hg _

end Hindman168
