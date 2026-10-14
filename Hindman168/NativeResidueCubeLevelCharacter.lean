import Hindman168.NativeCubeFaceLevelCharacter

/-! Horizontal obstructions for the actual rational-RESIDUE cube give
ORIGINAL rational level characters. Rational conjugation preserves the
original rational form, and does not require rho to belong to H. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_conjugate_subgroup_level_character_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ) :
    NativeSubgroupRationalLevelCharacter (nativeConjugateNilmanifoldData D ρ)
      (nativeConjugateSubgroupFiltration D F ρ hρ) j phi ↔
      NativeSubgroupRationalLevelCharacter D F j phi := by
  have he := rough_native_conjugate_log_span (E := D.E) (I := D.I) (G := D.G) D.Γ
    ((nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ ρ).mp hρ)
  rw [nativeLieExponential_globalLogarithm] at he
  constructor
  · rintro ⟨hne,hNext,hBracket,hRat⟩
    refine ⟨hne,hNext,hBracket,?_⟩
    intro v hv hvRat
    exact hRat v hv (he.symm ▸ hvRat)
  · rintro ⟨hne,hNext,hBracket,hRat⟩
    refine ⟨hne,hNext,hBracket,?_⟩
    intro v hv hvRat
    exact hRat v hv (he ▸ hvRat)

noncomputable def nativeResidueCubeFaceFunctional {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ) (A : Finset (Fin d)) : D.E →ₗ[ℝ] ℝ :=
  nativeCubeFaceFunctional (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e chi A

theorem native_residue_cube_horizontal_maximal_level {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeResidueCubeData D F ρ hρ d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeResidueCubeData D F ρ hρ d n e).I)
      (nativeResidueCubeData D F ρ hρ d n e).Γ chi) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ A : Finset (Fin d), A.card ≤ j ∧
      NativeSubgroupRationalLevelCharacter D F j (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi A) ∧
      ∀ k : ℕ, j < k → ∀ B : Finset (Fin d), B.card ≤ k →
        F.layer k ≤ (nativeResidueCubeFaceFunctional D F ρ hρ d n e chi B).ker := by
  obtain ⟨j,hj,hjTop,A,hA,hLevel,hTail⟩ := native_cube_horizontal_face_maximal_level
    (nativeConjugateNilmanifoldData D ρ) (nativeConjugateSubgroupFiltration D F ρ hρ) d n e chi hChi
  exact ⟨j,hj,hjTop,A,hA,
    (native_conjugate_subgroup_level_character_iff D F ρ hρ j _).mp hLevel,hTail⟩

end Hindman168
