import Hindman168.NativeTerminalRelativePairObservable
import Hindman168.NativeTerminalProductPairTranslation
import Hindman168.NativeRelativeFirstTerminalTranslation
import Hindman168.NativeRelativeTerminalSubgroup

/-! SAME ACTUAL relative pair satisfies first-coordinate terminal
eigenlaw and exact ORIGINAL terminal-diagonal subgroup invariance. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_terminal_relative_pair_first_equivariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : roughStretchedLowerCentralFiltration D.G d (s*d))
      (q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ),
      nativeTerminalRelativePairObservable D d hd k g F (nativeRelativeFirstTerminalElement D d hd hdeg z • q) =
        UnitAddTorus.mFourier k (nativeOriginalTerminalTorusProjection D d hd z) *
          nativeTerminalRelativePairObservable D d hd k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  rw [native_terminal_relative_pair_observable_apply,native_terminal_relative_pair_observable_apply,
    native_relative_product_coset_map_equivariant,native_relative_first_terminal_element_apply]
  exact native_terminal_product_pair_first_equivariant D d hd k g F z (nativeRelativeProductCosetMap D d hd q)

theorem native_terminal_relative_pair_subgroup_invariant {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (k : nativeOriginalTerminalIndex D d → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRelativeTerminalSubgroup D d hd)
      (q : (nativeRelativeSquareData D d hd 1).G ⧸ (nativeRelativeSquareData D d hd 1).Γ),
      nativeTerminalRelativePairObservable D d hd k g F ((z : (nativeRelativeSquareData D d hd 1).G) • q) =
        nativeTerminalRelativePairObservable D d hd k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have ht := relative_square_internal_terminal_diagonal
    (roughStretchedLowerCentralFiltration D.G d) (rough_stretched_filtration_normal d) (s*d)
    (rough_stretched_filtration_terminal d hd D.step_le)
  have hp := Eq.mp (congrArg (fun N : Subgroup (nativeRelativeSquareData D d hd 1).G =>
    (z : (nativeRelativeSquareData D d hd 1).G) ∈ N) ht) z.property
  obtain ⟨h1,he⟩ := (relative_diagonal_mem_iff _
    (nativeRelativeGroupInclusion D d hd 1 (z : (nativeRelativeSquareData D d hd 1).G))).mp hp
  let w : roughStretchedLowerCentralFiltration D.G d (s*d) :=
    ⟨(nativeRelativeGroupInclusion D d hd 1 (z : (nativeRelativeSquareData D d hd 1).G)).1,h1⟩
  have hw : nativeRelativeGroupInclusion D d hd 1 (z : (nativeRelativeSquareData D d hd 1).G) =
      ((w : D.G),(w : D.G)) := Prod.ext rfl he.symm
  rw [native_terminal_relative_pair_observable_apply,native_terminal_relative_pair_observable_apply,
    native_relative_product_coset_map_equivariant,hw]
  exact native_terminal_product_pair_diagonal_invariant D d hd k g F w (nativeRelativeProductCosetMap D d hd q)

end Hindman168
