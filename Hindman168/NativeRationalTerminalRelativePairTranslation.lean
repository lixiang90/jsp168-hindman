import Hindman168.NativeRationalTerminalRelativePairObservable
import Hindman168.NativeRationalTerminalProductPairTranslation
import Hindman168.NativeRationalRelativeTerminalGeometry

/-! SAME ACTUAL relative pair satisfies first-coordinate terminal
eigenlaw and exact ORIGINAL terminal-diagonal subgroup invariance. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_relative_pair_first_equivariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalFilteredGroupLayer D L (ℓ))
      (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalRelativePairObservable D L k g F (nativeRationalRelativeFirstTerminalElement D L hdeg z • q) =
        UnitAddTorus.mFourier k (nativeRationalTerminalTorusProjection D L z) *
          nativeRationalTerminalRelativePairObservable D L k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  rw [native_rational_terminal_relative_pair_observable_apply,native_rational_terminal_relative_pair_observable_apply,
    native_rational_relative_product_coset_map_equivariant,native_rational_relative_first_terminal_element_apply]
  exact native_rational_terminal_product_pair_first_equivariant D L k g F z (nativeRationalRelativeProductCosetMap D L q)

theorem native_rational_terminal_relative_pair_subgroup_invariant {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (k : nativeRationalTerminalIndex D L → ℤ) (g : D.G) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C(D.G ⧸ D.Γ,ℂ)) (z : nativeRationalTerminalSubgroup (nativeRationalRelativeData D L 1) (nativeRelativeRationalLieFiltration D L))
      (q : (nativeRationalRelativeData D L 1).G ⧸ (nativeRationalRelativeData D L 1).Γ),
      nativeRationalTerminalRelativePairObservable D L k g F ((z : (nativeRationalRelativeData D L 1).G) • q) =
        nativeRationalTerminalRelativePairObservable D L k g F q := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F z q
  have hz := Eq.mp (congrArg (fun N : Subgroup (nativeRationalRelativeData D L 1).G =>
    z.val ∈ N) (native_rational_relative_terminal_subgroup_eq D L)) z.property
  have ht := relative_square_internal_terminal_diagonal
    (nativeRationalFilteredGroupLayer D L) (native_rational_filtered_group_normal D L) (ℓ)
    (native_rational_filtered_group_terminal D L)
  have hp := Eq.mp (congrArg (fun N : Subgroup (nativeRationalRelativeData D L 1).G =>
    (z : (nativeRationalRelativeData D L 1).G) ∈ N) ht) hz
  obtain ⟨h1,he⟩ := (relative_diagonal_mem_iff _
    (nativeRationalRelativeGroupInclusion D L 1 (z : (nativeRationalRelativeData D L 1).G))).mp hp
  let w : nativeRationalFilteredGroupLayer D L (ℓ) :=
    ⟨(nativeRationalRelativeGroupInclusion D L 1 (z : (nativeRationalRelativeData D L 1).G)).1,h1⟩
  have hw : nativeRationalRelativeGroupInclusion D L 1 (z : (nativeRationalRelativeData D L 1).G) =
      ((w : D.G),(w : D.G)) := Prod.ext rfl he.symm
  rw [native_rational_terminal_relative_pair_observable_apply,native_rational_terminal_relative_pair_observable_apply,
    native_rational_relative_product_coset_map_equivariant,hw]
  exact native_rational_terminal_product_pair_diagonal_invariant D L k g F w (nativeRationalRelativeProductCosetMap D L q)

end Hindman168
