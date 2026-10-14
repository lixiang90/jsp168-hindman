import Hindman168.NativeRationalRelativeExponentialLogarithm
import Hindman168.NativeProductAdjointDifferential
import Hindman168.RelativeLinearFiltration

/-! Actual internal relative Lie layers for ANY original rational Lie
filtration, with genuine bracket and logarithmic membership transport. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalRelativeLieLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    Submodule ℝ (nativeRationalRelativeData D F 1).E :=
  (relativeLinearFiltration F.layer i).comap (nativeRationalRelativeModelInclusion D F 1).toLinearMap

noncomputable def nativeRationalRelativeInternalGroupLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ) :
    Subgroup (nativeRationalRelativeData D F 1).G :=
  relativeSquareInternalFiltration (nativeRationalFilteredGroupLayer D F) (native_rational_filtered_group_normal D F) i

theorem native_rational_relative_lie_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    Antitone (nativeRationalRelativeLieLayer D F) := by
  intro i j hij
  exact Submodule.comap_mono ((relative_linear_filtration_antitone F.layer F.antitone) hij)

theorem native_rational_relative_lie_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalRelativeLieLayer D F 0 = ⊤ := by
  simp only [nativeRationalRelativeLieLayer,relative_linear_filtration_zero F.layer F.zero F.one,Submodule.comap_top]

theorem native_rational_relative_lie_one {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) :
    nativeRationalRelativeLieLayer D F 1 = ⊤ := by
  apply top_unique
  intro v _
  change nativeRationalRelativeModelInclusion D F 1 v ∈ relativeLinearFiltration F.layer 1
  rw [← native_rational_relative_subalgebra_model D F 1]
  exact v.property

theorem native_rational_relative_adjoint_differential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (v w : (nativeRationalRelativeData D F 1).E) :
    nativeRationalRelativeModelInclusion D F 1
      (nativeLieAdjointDifferential (I := (nativeRationalRelativeData D F 1).I)
        (G := (nativeRationalRelativeData D F 1).G) v w) =
    nativeLieAdjointDifferential (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeRationalRelativeModelInclusion D F 1 v) (nativeRationalRelativeModelInclusion D F 1 w) := by
  have he := nativeSmoothHom_generator_intertwine
    (E := (nativeRationalRelativeData D F 1).E) (F := D.E × D.E)
    (I := (nativeRationalRelativeData D F 1).I) (J := D.I.prod D.I)
    (nativeRationalRelativeGroupInclusion D F 1) (native_rational_relative_inclusion_contMDiff D F 1) v w
  rw [native_rational_relative_inclusion_mfderiv] at he
  simpa only [nativeLieAdjointGenerator_eq_differential] using he

theorem native_rational_relative_lie_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {i j : ℕ} {v w : (nativeRationalRelativeData D F 1).E}
    (hv : v ∈ nativeRationalRelativeLieLayer D F i) (hw : w ∈ nativeRationalRelativeLieLayer D F j) :
    nativeLieAdjointDifferential (I := (nativeRationalRelativeData D F 1).I)
      (G := (nativeRationalRelativeData D F 1).G) v w ∈ nativeRationalRelativeLieLayer D F (i+j) := by
  change nativeRationalRelativeModelInclusion D F 1
    (nativeLieAdjointDifferential (I := (nativeRationalRelativeData D F 1).I)
      (G := (nativeRationalRelativeData D F 1).G) v w) ∈ relativeLinearFiltration F.layer (i+j)
  rw [native_rational_relative_adjoint_differential,
    native_product_adjoint_differential (I := D.I) (J := D.I) (G := D.G) (K := D.G)]
  exact relative_linear_filtration_bilinear F.layer
    (nativeLieAdjointDifferential (I := D.I) (G := D.G)) F.bracket hv hw

theorem native_rational_relative_internal_logarithm_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ) (i : ℕ)
    (g : (nativeRationalRelativeData D F 1).G) :
    g ∈ nativeRationalRelativeInternalGroupLayer D F i ↔
      nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D F 1).E)
        (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G) g ∈
          nativeRationalRelativeLieLayer D F i := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  change nativeRationalRelativeGroupInclusion D F 1 g ∈ nativeRationalRelativeGroupLayer D F i ↔ _
  rw [← native_rational_relative_native_subgroup_eq D F i,
    nativeLieSubalgebraSubgroup_mem_globalLogarithm_iff,native_rational_relative_subalgebra_model]
  change _ ↔ nativeRationalRelativeModelInclusion D F 1
    (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D F 1).E)
      (I := (nativeRationalRelativeData D F 1).I) (G := (nativeRationalRelativeData D F 1).G) g) ∈
        relativeLinearFiltration F.layer i
  rw [native_rational_relative_data_logarithm]

end Hindman168
