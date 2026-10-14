import Hindman168.NativeRelativeDiagonalInclusion
import Hindman168.NativeLieLayerLatticeCompact

/-! ACTUAL terminal subspace is RATIONAL against ACTUAL ORIGINAL
relative restricted lattice. Genuine original positive powers and exact
relative Exp inclusion preserve rational directions; they span the full V. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_diagonal_rational_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) {v : D.E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRelativeDiagonalInclusion D d hd v ∈ nativeSubgroupRationalLogSpan
      (E := (nativeRelativeSquareData D d hd 1).E) (I := (nativeRelativeSquareData D d hd 1).I)
      (nativeRelativeSquareData D d hd 1).Γ := by
  obtain ⟨n,hn,hp⟩ := (nativeSubgroupRationalLogSpan_mem_iff_positive_power (I := D.I) D.Γ v).mp hv
  apply (nativeSubgroupRationalLogSpan_mem_iff_positive_power
    (E := (nativeRelativeSquareData D d hd 1).E) (I := (nativeRelativeSquareData D d hd 1).I)
    (nativeRelativeSquareData D d hd 1).Γ (nativeRelativeDiagonalInclusion D d hd v)).mpr
  refine ⟨n,hn,?_⟩
  have he : nativeRelativeGroupInclusion D d hd 1
      (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
        (nativeRelativeDiagonalInclusion D d hd v)) =
      nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G) (v,v) :=
    native_relative_data_exponential D d hd 1 (nativeRelativeDiagonalInclusion D d hd v)
  have he' := he.trans (nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G) (v,v))
  have hpow := (map_pow (nativeRelativeGroupInclusion D d hd 1)
    (nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (G := (nativeRelativeSquareData D d hd 1).G)
      (nativeRelativeDiagonalInclusion D d hd v)) n).trans (congrArg (fun p : D.G × D.G => p^n) he')
  exact Eq.mpr (congrArg (fun p : D.G × D.G => p ∈ D.Γ.prod D.Γ) hpow) ⟨hp,hp⟩

theorem native_relative_terminal_model_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    nativeLatticeRationalSubspace (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ
        (nativeRelativeTerminalModel D d hd) := by
  let A := nativeLieLowerCentralModel (I := D.I) (G := D.G) (((s*d) ⌈/⌉ d)-1)
  let W := nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ
  have hA : Submodule.span ℝ ((A.restrictScalars ℚ ⊓ W : Submodule ℚ D.E) : Set D.E) = A :=
    nativeLieLowerCentralModel_lattice_rational (I := D.I) D.Γ (((s*d) ⌈/⌉ d)-1)
  unfold nativeLatticeRationalSubspace
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun _ hv => hv.1)
  · conv_lhs => rw [native_relative_terminal_model_eq_map D d hd]
    change A.map (nativeRelativeDiagonalInclusion D d hd).toLinearMap ≤ _
    rw [← hA,Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨v,hv,rfl⟩
    apply Submodule.subset_span
    refine ⟨?_,native_relative_diagonal_rational_mem D d hd hv.2⟩
    change (v,v) ∈ diagonalLinearModel A
    exact diagonal_linear_model_diagonal_mem A hv.1

end Hindman168
