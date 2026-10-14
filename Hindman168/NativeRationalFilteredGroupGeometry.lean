import Hindman168.NativeRationalFilteredGroupBrackets
import Hindman168.NativeRationalLatticeCompact
import Hindman168.NativeRelativeReducedLayerTopology

/-! Actual finite rational group filtration geometry, with explicit original
and reduced-image group-layer identifications. No inverse input is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_filtered_group_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalFilteredGroupLayer D F 0 = ⊤ := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff,F.zero]
  simp only [Submodule.mem_top,Subgroup.mem_top]

theorem native_rational_filtered_group_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalFilteredGroupLayer D F 1 = ⊤ := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff,F.one]
  simp only [Submodule.mem_top,Subgroup.mem_top]

theorem native_rational_filtered_group_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalFilteredGroupLayer D F (ℓ+1) = ⊥ := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff,F.terminal,Submodule.mem_bot,Subgroup.mem_bot]
  constructor
  · intro hg
    exact (nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) g).symm.trans
      ((congrArg (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)) hg).trans
        (nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)))
  · rintro rfl
    exact nativeLieGlobalLogarithm_one (E := D.E) (I := D.I) (G := D.G)

theorem native_rational_filtered_group_closed {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    IsClosed (nativeRationalFilteredGroupLayer D F i : Set D.G) :=
  nativeLieSubalgebraSubgroup_closed (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra

theorem native_rational_filtered_group_contractible {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    ContractibleSpace (nativeRationalFilteredGroupLayer D F i) :=
  nativeLieSubalgebraSubgroup_contractible (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra

theorem native_rational_filtered_group_lattice_discrete {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    DiscreteTopology (D.Γ.comap (nativeRationalFilteredGroupLayer D F i).subtype) :=
  nativeLieLattice_intersection_discrete D.Γ (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra

theorem native_rational_filtered_group_lattice_cocompact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    CompactSpace ((nativeRationalFilteredGroupLayer D F i) ⧸
      D.Γ.comap (nativeRationalFilteredGroupLayer D F i).subtype) :=
  nativeRationalLieLattice_quotient_compact D.Γ (nativeRationalFilteredLieIdeal D F i).toLieSubalgebra (F.rational i)

theorem native_original_rational_filtered_group_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeRationalFilteredGroupLayer D (nativeOriginalRationalLieFiltration D d hd) i =
      roughStretchedLowerCentralFiltration D.G d i := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff]
  exact (rough_native_stretched_filtration_mem_log_iff (I := D.I) d i g).symm

theorem native_reduced_rational_filtered_group_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeRationalFilteredGroupLayer (nativeRelativeReducedData D d hd)
      (nativeReducedRationalLieFiltration D d hd) i = nativeRelativeReducedNativeFiltration D d hd i := by
  ext g
  rw [native_rational_filtered_group_logarithm_iff,native_relative_reduced_layer_logarithm_iff]
  rfl

end Hindman168
