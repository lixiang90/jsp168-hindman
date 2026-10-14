import Hindman168.AlignmentCanonicalPointOrbit
import Hindman168.AlignmentOriginalNativeCubeState
import Hindman168.NativeOriginalLinearOrbitPolynomial

/-! The full finite joint orbit retains heterogeneous ORIGINAL targets and
their individual tail products. All factors use one actual native product
at the original step s. No marginal invariance assertion is made here. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentOriginalJointPointBase
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeFinitePiGroupValue _ (fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
    (alignmentNativeModelArray (n ν) (v ν) (hv ν) (g ν) (a ν)
      (alignmentCanonicalPointExponent y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) (T ν) p (shift ν))
      (fun e => if e.targetTail = T ν then alignmentPairProgression q₀ w (F.modulus w) e y else 0)))

noncomputable def alignmentOriginalJointPointStep
    (T : ι → Finset (Fin N)) (y : Fin N → ℕ) (g : ∀ ν, (D ν).G) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeFinitePiGroupValue _ (fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
    (alignmentNativeConstantArray (n ν) (v ν) (hv ν) (g ν ^ (alignmentNaturalBlockProduct y (T ν) : ℤ))))

noncomputable def alignmentOriginalJointPointOrbit
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  alignmentOriginalJointPointStep D n v hv T y g ^ ell *
    alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a

theorem alignment_original_joint_point_orbit_component
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) (ν : ι) :
    nativeFinitePiGroupEquiv _
      (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell) ν =
      alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
        (alignmentNativeModelOrbit (n ν) (v ν) (hv ν) (g ν) (a ν)
          (alignmentCanonicalPointExponent y (F.modulus w)
            (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) (T ν) p (shift ν))
          (alignmentNaturalBlockProduct y (T ν))
          (fun e => if e.targetTail = T ν then alignmentPairProgression q₀ w (F.modulus w) e y else 0) ell) := by
  exact congrArg (alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν))
    (alignmentNativeModelOrbit_linear (n ν) (v ν) (hv ν) (g ν) (a ν) _ _ _ ell).symm

theorem alignment_original_joint_point_orbit_log_source
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    nativeLieExponential (E := J.E) (I := J.I) (G := J.G)
      (roughVectorMvEval (E := J.E) (nativeOriginalLeftLinearLog J
        (alignmentOriginalJointPointStep D n v hv T y g)
        (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)) (fun _ => (ell : ℝ))) =
      alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a ell :=
  native_original_left_linear_integer_source _ _ _ ell

theorem alignment_original_joint_point_orbit_log_adapted
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := J.I) (G := J.G) 1)
      (nativeOriginalLeftLinearLog J (alignmentOriginalJointPointStep D n v hv T y g)
        (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)) 0 :=
  native_original_left_linear_log_weighted _ _ _

end Hindman168

