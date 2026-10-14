import Hindman168.NativeRelativeLieLayerLogarithm
import Hindman168.NativeRelativeReducedNativeFiltration
import Hindman168.NativeRelativeReductionExponentialLogarithm

/-! The reduced filtration uses the actual projected relative Lie layers.
It is not replaced by a stretched lower central series. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRelativeReducedLieFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    Submodule ℝ (nativeRelativeReducedData D d hd).E :=
  (nativeRelativeLieFiltration D d hd i).map
    (nativeRelativeReductionModelProjection D d hd).toLinearMap

theorem native_relative_reduced_lie_filtration_antitone {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Antitone (nativeRelativeReducedLieFiltration D d hd) := by
  intro i j hij
  exact Submodule.map_mono ((native_relative_lie_filtration_antitone D d hd) hij)

theorem native_relative_reduced_layer_logarithm_iff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (g : (nativeRelativeReducedData D d hd).G) :
    g ∈ nativeRelativeReducedNativeFiltration D d hd i ↔
      nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I)
        (G := (nativeRelativeReducedData D d hd).G) g ∈ nativeRelativeReducedLieFiltration D d hd i := by
  letI := native_relative_terminal_subgroup_normal D d hd
  change g ∈ (nativeRelativeSquareInternalFiltration D d i).map
    (nativeRelativeReductionGroupProjection D d hd) ↔ _
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [native_relative_reduction_data_logarithm]
    exact Submodule.mem_map_of_mem
      ((native_relative_internal_layer_logarithm_iff D d hd i a).mp ha)
  · rintro ⟨v,hv,he⟩
    refine ⟨nativeLieExponential (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I)
      (G := (nativeRelativeSquareData D d hd 1).G) v,
      native_relative_lie_filtration_exponential_mem D d hd i hv,?_⟩
    rw [native_relative_reduction_data_exponential]
    exact (congrArg (nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) he).trans
        (nativeLieExponential_globalLogarithm (E := (nativeRelativeReducedData D d hd).E)
          (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G) g)

theorem native_relative_reduced_lie_filtration_exponential_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    {v : (nativeRelativeReducedData D d hd).E}
    (hv : v ∈ nativeRelativeReducedLieFiltration D d hd i) :
    nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
      (I := (nativeRelativeReducedData D d hd).I)
      (G := (nativeRelativeReducedData D d hd).G) v ∈ nativeRelativeReducedNativeFiltration D d hd i := by
  apply (native_relative_reduced_layer_logarithm_iff D d hd i _).mpr
  simpa only [nativeLieGlobalLogarithm_exponential] using hv

theorem native_relative_reduced_lie_filtration_bracket {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {i j : ℕ} {v w : (nativeRelativeReducedData D d hd).E}
    (hv : v ∈ nativeRelativeReducedLieFiltration D d hd i)
    (hw : w ∈ nativeRelativeReducedLieFiltration D d hd j) :
    nativeLieAdjointDifferential (I := (nativeRelativeReducedData D d hd).I)
      (G := (nativeRelativeReducedData D d hd).G) v w ∈ nativeRelativeReducedLieFiltration D d hd (i+j) := by
  obtain ⟨a,ha,rfl⟩ := hv
  obtain ⟨b,hb,rfl⟩ := hw
  have he := nativeSmoothHom_generator_intertwine
    (E := (nativeRelativeSquareData D d hd 1).E) (F := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeSquareData D d hd 1).I) (J := (nativeRelativeReducedData D d hd).I)
    (nativeRelativeReductionGroupProjection D d hd)
    (native_relative_reduction_projection_contMDiff D d hd) a b
  rw [native_relative_reduction_projection_mfderiv] at he
  simp only [nativeLieAdjointGenerator_eq_differential] at he
  exact he ▸ (Submodule.mem_map_of_mem (native_relative_lie_filtration_bracket D d hd ha hb))

theorem native_relative_reduced_lie_filtration_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) (hi : s*d ≤ i) :
    nativeRelativeReducedLieFiltration D d hd i = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have hm := native_relative_reduced_lie_filtration_exponential_mem D d hd i hv
  rw [native_relative_reduced_native_filtration_beyond_terminal D d hd i hi,Subgroup.mem_bot] at hm
  have he := congrArg (nativeLieGlobalLogarithm (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)) hm
  simpa only [nativeLieGlobalLogarithm_exponential,nativeLieGlobalLogarithm_one,Submodule.mem_bot] using he

end Hindman168
