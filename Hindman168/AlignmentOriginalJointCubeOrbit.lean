import Hindman168.AlignmentOriginalJointLinearOrbit
import Hindman168.NativeOriginalLinearOrbitAdapted

/-! The original all-target cube readings are vertices of ONE common
joint point orbit. Targets may differ; each keeps its own tail product,
residue correction and progression table. Zero/one vertex profiles are
specializations of the exact integer-weight identity. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentOriginalJointCubeGroup
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeFinitePiGroupValue _ (fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
    (alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
      (T ν) p Y (ell none) (fun j => ell (some j)) (weight ν) (shift ν)))

theorem alignment_original_joint_cube_point_component
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) (ν : ι) :
    nativeFinitePiGroupEquiv _
      (alignmentOriginalJointCubeGroup D n v hv F q₀ w T y p Y shift weight g a ell) ν =
      nativeFinitePiGroupEquiv _
        (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a
          (ell none + ∑ j, weight ν j * ell (some j))) ν := by
  rw [alignment_original_joint_point_orbit_component]
  exact congrArg (alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν))
    (alignment_native_canonical_cube_point_orbit (n ν) (v ν) (hv ν)
      (g ν) (a ν) y (F.modulus w) _ _ (T ν) p Y (ell none)
      (fun j => ell (some j)) (weight ν) (shift ν))

theorem alignment_original_joint_cube_common_vertex
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    alignmentOriginalJointCubeGroup D n v hv F q₀ w T y p Y shift (fun _ => weight) g a ell =
      alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a
        (ell none + ∑ j, weight j * ell (some j)) := by
  apply (nativeFinitePiGroupEquiv _).injective
  funext ν
  exact alignment_original_joint_cube_point_component D n v hv F q₀ w T y p Y shift
    (fun _ => weight) g a ell ν

theorem alignment_original_joint_cube_uniform_target_quotient
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (alignmentOriginalJointCubeGroup D n v hv F q₀ w (fun _ => T) y p Y shift weight g a ell : J.G ⧸ J.Γ) =
      alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell := rfl

theorem alignment_original_joint_point_lower_central_adapted
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    RoughFilteredPolynomial (nilLowerCentralFiltration J.G)
      (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a) :=
  native_original_left_linear_integer_adapted _ _ _

theorem alignment_original_joint_point_coefficient_adapted
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (I : Unit →₀ ℕ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    roughVectorMvCoefficient (nativeOriginalLeftLinearLog J
      (alignmentOriginalJointPointStep D n v hv T y g)
      (alignmentOriginalJointPointBase D n v hv F q₀ w T y p shift g a)) I ∈
        nativeLieLowerCentralModel (I := J.I) (G := J.G) (I.sum (fun _ m => m)-1) :=
  native_original_left_linear_coefficient_adapted _ _ _ I

end Hindman168
