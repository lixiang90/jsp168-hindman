import Hindman168.NativeDiagonalCenterModel
import Hindman168.NativeCenterLatticeCoordinates
import Hindman168.NativeSubgroupLogarithmSpan

/-! ACTUAL original center-lattice columns embedded diagonally span the
actual model; their product exponentials belong to ORIGINAL product lattice. -/

namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeDiagonalLatticeColumn {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := D.I) (G := D.G)))) : D.E × D.E :=
  nativeDiagonalCenterInclusion D (nativeCenterLatticeRealBasis (I := D.I) D.Γ i)

theorem native_diagonal_lattice_column_mem_model {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := D.I) (G := D.G)))) :
    nativeDiagonalLatticeColumn D i ∈ nativeDiagonalCenterModel D :=
  ⟨nativeCenterLatticeRealBasis (I := D.I) D.Γ i,rfl⟩

theorem native_diagonal_lattice_column_exponential_mem {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := D.I) (G := D.G)))) :
    nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalLatticeColumn D i) ∈ D.Γ.prod D.Γ := by
  rw [nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G)]
  exact ⟨native_center_lattice_basis_exponential_mem (I := D.I) D.Γ i,
    native_center_lattice_basis_exponential_mem (I := D.I) D.Γ i⟩

theorem native_diagonal_lattice_column_rational_mem {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (i : Fin (Module.finrank ℝ (nativeLieCenterModel (I := D.I) (G := D.G)))) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeDiagonalLatticeColumn D i ∈ nativeSubgroupRationalLogSpan (E := D.E × D.E)
      (I := D.I.prod D.I) (G := D.G × D.G) (D.Γ.prod D.Γ) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have h := nativeSubgroup_logarithm_mem_span (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
    (D.Γ.prod D.Γ) (native_diagonal_lattice_column_exponential_mem D i)
  rw [nativeLieGlobalLogarithm_exponential (E := D.E × D.E)] at h
  exact h

theorem native_diagonal_lattice_columns_span {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    Submodule.span ℝ (Set.range (nativeDiagonalLatticeColumn D)) = nativeDiagonalCenterModel D := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact native_diagonal_lattice_column_mem_model D i
  · intro v hv
    obtain ⟨w,rfl⟩ := (native_diagonal_center_model_mem D v).mp hv
    let b := nativeCenterLatticeRealBasis (I := D.I) D.Γ
    change nativeDiagonalCenterInclusion D w ∈ Submodule.span ℝ (Set.range (nativeDiagonalLatticeColumn D))
    rw [← b.sum_repr w,map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact (Submodule.span ℝ (Set.range (nativeDiagonalLatticeColumn D))).smul_mem _
      (Submodule.subset_span ⟨i,rfl⟩)

end Hindman168
