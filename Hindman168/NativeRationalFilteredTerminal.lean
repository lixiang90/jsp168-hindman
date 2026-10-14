import Hindman168.NativeRationalFilteredGroupGeometry
import Hindman168.NativeCentralSubspaceQuotientLattice

/-! The genuine terminal layer of ANY actual finite rational Lie
filtration is central and rational. Its ACTUAL image lattice is discrete
and cocompact, supplying the true quotient construction for recursion. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_filtered_terminal_central {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    F.layer ℓ ≤ nativeLieCenterModel (I := D.I) (G := D.G) := by
  intro v hv
  apply (nativeLieCenterModel_mem_iff_generator_eq_zero (I := D.I) (G := D.G) v).mpr
  apply ContinuousLinearMap.ext
  intro w
  rw [nativeLieAdjointGenerator_eq_differential]
  have hw : w ∈ F.layer 1 := by rw [F.one]; exact Submodule.mem_top
  have hm := F.bracket ℓ 1 v w hv hw
  rw [F.terminal,Submodule.mem_bot] at hm
  exact hm

noncomputable def nativeRationalTerminalSubgroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) : Subgroup D.G :=
  nativeCentralSubspaceSubgroup (I := D.I) (F.layer ℓ) (native_rational_filtered_terminal_central D F)

theorem native_rational_terminal_subgroup_eq {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalTerminalSubgroup D F = nativeRationalFilteredGroupLayer D F ℓ := by
  ext g
  exact (nativeCentralSubspaceSubgroup_mem_logarithm (I := D.I) _ _ g).trans
    (native_rational_filtered_group_logarithm_iff D F ℓ g).symm

theorem native_rational_terminal_subgroup_normal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    (nativeRationalTerminalSubgroup D F).Normal :=
  nativeCentralSubspaceSubgroup_normal (I := D.I) _ _

theorem native_rational_terminal_subgroup_closed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    IsClosed (nativeRationalTerminalSubgroup D F : Set D.G) :=
  nativeCentralSubspaceSubgroup_closed (I := D.I) _ _

theorem native_rational_terminal_image_lattice_discrete {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    DiscreteTopology (D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))) := by
  letI := native_rational_terminal_subgroup_normal D F
  exact nativeCentralSubspaceQuotient_lattice_image_discrete (I := D.I) D.Γ (F.layer ℓ)
    (native_rational_filtered_terminal_central D F) (F.rational ℓ)

theorem native_rational_terminal_image_lattice_cocompact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    letI := native_rational_terminal_subgroup_normal D F
    CompactSpace ((D.G ⧸ nativeRationalTerminalSubgroup D F) ⧸
      D.Γ.map (QuotientGroup.mk' (nativeRationalTerminalSubgroup D F))) := by
  letI := native_rational_terminal_subgroup_normal D F
  exact nativeCentralSubspaceQuotient_lattice_image_cocompact (I := D.I) D.Γ (F.layer ℓ)
    (native_rational_filtered_terminal_central D F)

end Hindman168
