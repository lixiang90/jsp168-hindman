import Hindman168.AlignmentNativeCubeProjectionFace
import Hindman168.AlignmentOriginalNativeCubeMeans

/-! Exact original empirical means after the proved cube projection. The
sample grid, residue classes and normalization are unchanged. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_original_native_cube_projected_mean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (d : ℕ)
    (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (g a : ∀ ν, (D ν).G)
    (obs : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ → ℂ) :
    alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a obs =
      finiteComplexSetMean (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d)
        (fun ell => obs (nativeFinitePiCubeProjection
          (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
          (fun ν => alignmentBinaryCubeVertex (weight ν))
          (fun V => (alignmentOriginalJointPointOrbit D n v hv F q₀ w (fun _ => T) y p shift g a
            (ell none+∑ j ∈ V, ell (some j)) :
              (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
              (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)))) := by
  unfold alignmentOriginalNativeCubeMean
  rw [FiniteMass.complexExpectation_uniformFinset]
  congr 1
  funext ell
  rw [alignment_original_native_cube_projection D n v hv F q₀ w T y p Y shift weight hw g a ell]

end Hindman168
