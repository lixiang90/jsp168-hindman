import Hindman168.AlignmentJointNativeCylinderPresentation
import Hindman168.AlignmentOriginalContinuousCubeMean

/-! Literal original cube states in the genuine native product quotient.
Every integer slot equals the original nilsequence argument, with the original
modulus/residues/progressions. Integer Y is explicit, never rational division. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentOriginalNativeCubeState
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ :=
  QuotientGroup.mk (nativeFinitePiGroupValue
    (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
      (alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
        T p Y (ell none) (fun j => ell (some j)) (weight ν) (shift ν))))

theorem alignment_original_native_cube_state_reading
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ)
    (ν : ι) (slot : AlignmentAddingPair N i → ℤ) :
    alignmentJointNativeCosetEvaluation D n v hv ν slot
      (alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell) =
      (g ν ^ (alignmentIntegerArrayArgument y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
        (p+(F.modulus w : ℤ)*(ell none+∑ j, weight ν j*ell (some j)))
        (shift ν) slot/(F.modulus w : ℤ)) * a ν : (D ν).G ⧸ (D ν).Γ) := by
  change (((alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
    (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
    T p Y (ell none) (fun j => ell (some j)) (weight ν) (shift ν)).val slot : (D ν).G ⧸ (D ν).Γ)) = _
  exact congrArg (fun h : (D ν).G => (h : (D ν).G ⧸ (D ν).Γ))
    (alignmentNativeCanonicalCubeArray_evaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G)
      (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w) (F.modulus w).pos
      _ _ T p Y (ell none) (fun j => ell (some j)) (weight ν) (shift ν) slot)

theorem alignment_original_native_cube_state_Y_invariant
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y Y' : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell=
      alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y' shift weight g a ell := by
  apply (alignment_joint_native_all_slot_readings_eq_iff D n v hv _ _).mp
  intro ν slot
  rw [alignment_original_native_cube_state_reading,alignment_original_native_cube_state_reading]

end Hindman168
