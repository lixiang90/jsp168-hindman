import Hindman168.NativeRationalDegreeRecursion
import Hindman168.NativeRationalRecursiveRelativeApplication

/-! The COMPLETE actual geometric degree recursion is applied to original
native data and to SAME retained original terminal quotient IMAGE data. -/

namespace Hindman168
universe u

noncomputable def nativeOriginalDegreeReductionStage {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (n : ℕ) :
    Σ D' : NativeNilmanifoldData.{u} s, NativeRationalLieFiltration D' (s*d-n) :=
  nativeIteratedRationalDegreeReduction D (nativeOriginalRationalLieFiltration D d hd) n

noncomputable def nativeOriginalImageDegreeReducedData {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) : NativeNilmanifoldData.{u} s :=
  nativeRationalDegreeReducedData (nativeRelativeReducedData D d hd) (nativeReducedRationalLieFiltration D d hd)

noncomputable def nativeOriginalImageDegreeReducedFiltration {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    NativeRationalLieFiltration (nativeOriginalImageDegreeReducedData D d hd) (s*d-1-1) :=
  nativeDegreeReducedRationalLieFiltration (nativeRelativeReducedData D d hd) (nativeReducedRationalLieFiltration D d hd)

theorem native_original_degree_reduction_terminates {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Subsingleton (nativeOriginalDegreeReductionStage D d hd (s*d)).1.G :=
  native_rational_degree_recursion_terminates D (nativeOriginalRationalLieFiltration D d hd)

theorem native_original_image_degree_reduced_layer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    (nativeOriginalImageDegreeReducedFiltration D d hd).layer i =
      ((relativeLinearFiltration (nativeRelativeReducedLieFiltration D d hd) i).comap
        (nativeRationalRelativeModelInclusion (nativeRelativeReducedData D d hd)
          (nativeReducedRationalLieFiltration D d hd) 1).toLinearMap).map
            (nativeRationalTerminalModelProjection (nativeRecursiveRelativeData D d hd)
              (nativeRecursiveRelativeLieFiltration D d hd)).toLinearMap := rfl

theorem native_original_image_degree_recursion_terminates {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Subsingleton (nativeIteratedRationalDegreeReduction (nativeRelativeReducedData D d hd)
      (nativeReducedRationalLieFiltration D d hd) (s*d-1)).1.G :=
  native_rational_degree_recursion_terminates (nativeRelativeReducedData D d hd) (nativeReducedRationalLieFiltration D d hd)

end Hindman168
