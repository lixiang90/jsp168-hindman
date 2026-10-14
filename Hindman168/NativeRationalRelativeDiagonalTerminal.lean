import Hindman168.NativeRationalRelativeCharacterSplitting
import Hindman168.NativeRationalTerminalCharacterPullback
import Hindman168.NativeRationalDegreeRecursion

/-! An actual reduced-quotient character's diagonal component kills the
ORIGINAL terminal layer, because its diagonal belongs to the TRUE relative
terminal layer. This does not assume diagonal nonzeroness. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_relative_diagonal_terminal_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (hv : v ∈ L.layer ℓ) :
    nativeRationalRelativeDiagonalModel D L v ∈ (nativeRelativeRationalLieFiltration D L).layer ℓ := by
  change (v,v) ∈ relativeLinearFiltration L.layer ℓ
  exact (relative_linear_model_mem_iff _ _ _).mpr
    ⟨hv,hv,by simp only [sub_self]; exact Submodule.zero_mem _⟩

theorem native_rational_relative_quotient_diagonal_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalDegreeReducedData D L).E →L[ℝ] ℝ)
    (v : D.E) (hv : v ∈ L.layer ℓ) :
    nativeRationalRelativeDiagonalCharacter D L
      (nativeRationalTerminalCharacterPullback (nativeRationalRelativeData D L 1)
        (nativeRelativeRationalLieFiltration D L) χ) v = 0 := by
  change χ (nativeRationalTerminalModelProjection (nativeRationalRelativeData D L 1)
    (nativeRelativeRationalLieFiltration D L) (nativeRationalRelativeDiagonalModel D L v)) = 0
  rw [(native_rational_terminal_model_projection_zero_iff _ _ _).mpr
    (native_rational_relative_diagonal_terminal_mem D L v hv)]
  exact map_zero χ

end Hindman168
