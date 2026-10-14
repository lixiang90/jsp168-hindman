import Hindman168.NativeSubgroupLevelCharacters
import Hindman168.RoughNativeCharacterNormalization
import Hindman168.RoughNativeConjugateLogSpan
import Mathlib.Data.Finset.Max

/-! The point-law horizontal obstruction has an actual greatest nonzero
filtration level. Its restriction is exactly a rational level character;
lattice-intersection integrality is transported in the ORIGINAL rational
form. These geometric implications supply no equidistribution premise. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_character_maximal_level {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hne : ∃ v ∈ F.layer 0, phi v ≠ 0)
    (hBracket : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (hRat : ∀ v ∈ F.layer 0, v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ →
      ∃ q : ℚ, phi v = (q : ℝ)) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ NativeSubgroupRationalLevelCharacter D F j phi ∧
      ∀ k : ℕ, j < k → F.layer k ≤ phi.ker := by
  classical
  let T := (Finset.Icc 1 ℓ).filter (fun j => ∃ v ∈ F.layer j, phi v ≠ 0)
  obtain ⟨v,hv,hphi⟩ := hne
  have hℓ : 1 ≤ ℓ := by
    by_contra hn
    have he : ℓ = 0 := by omega
    have hb : F.layer 0 = ⊥ := F.initial.trans (by simpa only [he] using F.terminal)
    rw [hb,Submodule.mem_bot] at hv
    exact hphi (hv ▸ phi.map_zero)
  have hT : T.Nonempty := by
    refine ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hℓ⟩,v,?_,hphi⟩⟩
    rwa [← F.initial]
  let j := T.max' hT
  have hjT : j ∈ T := T.max'_mem hT
  obtain ⟨hjRange,hjNonzero⟩ := Finset.mem_filter.mp hjT
  obtain ⟨hj,hjTop⟩ := Finset.mem_Icc.mp hjRange
  have hTail : ∀ k : ℕ, j < k → F.layer k ≤ phi.ker := by
    intro k hjk w hw
    by_cases hk : k ≤ ℓ
    · by_contra hbad
      have hkw : phi w ≠ 0 := hbad
      have hkT : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hk⟩,w,hw,hkw⟩
      have hkj : k ≤ j := T.le_max' k hkT
      omega
    · have hb : w ∈ F.layer (ℓ+1) := F.antitone (by omega) hw
      rw [F.terminal,Submodule.mem_bot] at hb
      exact hb ▸ phi.map_zero
  refine ⟨j,hj,hjTop,⟨hjNonzero,hTail (j+1) (by omega),?_,?_⟩,hTail⟩
  · intro a b _ _ _ x hx y hy
    exact hBracket x (F.antitone (Nat.zero_le a) hx) y (F.antitone (Nat.zero_le b) hy)
  · intro x hx hxRat
    exact hRat x (F.antitone (Nat.zero_le j) hx) hxRat

theorem native_subgroup_integral_character_rational_on_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hIntegral : ∀ g ∈ roughConjugateSubgroup D.Γ rho ⊓ nativeRationalSubgroupLayer D F i,
      ∃ m : ℤ, phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (m : ℝ)) :
    ∀ v ∈ F.layer i, v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ →
      ∃ q : ℚ, phi v = (q : ℝ) := by
  intro v hv hvRat
  apply rough_native_integral_character_rational_on_span (E := D.E) (I := D.I)
    (roughConjugateSubgroup D.Γ rho ⊓ nativeRationalSubgroupLayer D F i) phi hIntegral v
  change v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I)
    (roughConjugateSubgroup D.Γ rho ⊓
      nativeLieSubalgebraSubgroup (nativeRationalSubgroupLayerAlgebra D F i))
  rw [nativeSubgroupRationalLogSpan_inf_lieSubalgebra]
  have hSpan : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) (roughConjugateSubgroup D.Γ rho) =
      nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ := by
    have h := rough_native_conjugate_log_span (E := D.E) (I := D.I) D.Γ
      ((nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ rho).mp hRat)
    rwa [nativeLieExponential_globalLogarithm] at h
  rw [hSpan]
  exact ⟨hvRat,hv⟩

end Hindman168
