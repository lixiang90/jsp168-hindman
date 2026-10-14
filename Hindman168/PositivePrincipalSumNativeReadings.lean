import Hindman168.AlignmentJointNativeReadings
import Hindman168.AlignmentCanonicalPointOrbit
import Hindman168.AlignmentOriginalJointLinearOrbit
import Hindman168.AlignmentFrozenPieceReading

/-! Actual integer array arguments are read at the original quotient
exponent, including the residue correction. No orbit identification is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
attribute [local instance] alignmentAddingPairFintype

theorem principal_native_array_argument_quotient {N : ℕ} {i : Fin N}
    (t : Fin N → ℕ) (M : ℕ) (hM : 0 < M)
    (rho : AlignmentAddingPair N i → ℕ) (delta : AlignmentAddingPair N i → ℤ)
    (T : Finset (Fin N)) (p ell : ℤ) (shift slots : AlignmentAddingPair N i → ℤ) :
    alignmentIntegerArrayArgument t M rho delta T (p + (M : ℤ) * ell) shift slots / M =
      alignmentCanonicalPointExponent t M rho T p shift +
        (alignmentNaturalBlockProduct t T : ℤ) * ell +
        ∑ j, slots j * (if j.targetTail = T then delta j else 0) := by
  have h := alignmentIntegerArrayArgument_cube_quotient (κ := Empty) t M hM rho delta T
    p 0 ell (fun j => nomatch j) (fun j => nomatch j) shift slots
  simpa [alignmentCubeVertex, alignmentCubeBase, alignmentCanonicalPointExponent,
    alignmentIntegerArrayProgression, mul_ite, add_assoc, add_left_comm, add_comm] using h

universe u
variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν)))

/-- A reading on the SAME joint point orbit is the original observer at
its actual integer array argument divided by the original modulus. -/
theorem principal_native_joint_reading_integer_argument
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (x : Fin N → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) (ν : ι)
    (slots : AlignmentAddingPair N i → ℤ) (obs : (D ν).G ⧸ (D ν).Γ → ℝ) :
    obs (alignmentJointNativeCosetEvaluation D n v hv ν slots
      (QuotientGroup.mk (alignmentOriginalJointPointOrbit D n v hv F q₀ w T x p shift g a ell))) =
      obs ((g ν ^ (alignmentIntegerArrayArgument x (F.modulus w)
          (fun e => alignmentPairResidue q₀ w (F.modulus w) e x)
          (fun e => alignmentPairProgression q₀ w (F.modulus w) e x)
          (T ν) (p + (F.modulus w : ℤ) * ell) (shift ν) slots / (F.modulus w : ℤ)) *
        a ν : (D ν).G ⧸ (D ν).Γ)) := by
  change obs ((alignmentArrayNativeEvaluation (D ν) (n ν) (v ν) (hv ν) slots
    (nativeFinitePiGroupEquiv _
      (alignmentOriginalJointPointOrbit D n v hv F q₀ w T x p shift g a ell) ν) :
      (D ν).G ⧸ (D ν).Γ)) = _
  rw [alignment_original_joint_point_orbit_component]
  rw [principal_native_array_argument_quotient x (F.modulus w) (F.modulus w).pos]
  rfl

/-- The actual frozen piecewise nilsequence is a reading of the SAME
joint orbit. The original exposure-stability hypothesis supplies the piece
label; no equality of the piece function and a surrogate is assumed. -/
theorem principal_native_joint_frozen_piece_reading
    {d : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : ι → Finset (Fin N)) (ν : ι) (hT : ∀ j ∈ T ν, j < i)
    (C : ℕ) (V U : Finset (AlignmentAddingPair N i → ℤ))
    (x y : Fin N → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hcut : ∀ j, j < i → y j ≤ F.cutoff w j.val ^ 2)
    (hkey : alignmentShortExposureKey F w i (T ν) x = alignmentShortExposureKey F w i (T ν) y)
    (hgood : alignmentExposureArrayStable F w i q₀ C (T ν) V U x)
    (shift : ι → AlignmentAddingPair N i → ℤ) (hshift : shift ν ∈ V)
    (slots : AlignmentAddingPair N i → ℤ) (hslots : slots ∈ U)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (hdist : |p + (F.modulus w : ℤ) * ell - y i| ≤
      (C * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) : ℕ))
    (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
    (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G) :
    let label := fun ν =>
      ((((alignmentNaturalBlockProduct x (T ν) * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ)),
        alignmentPivotArrayResidue x (T ν) (F.modulus w) (x i)
          (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) (shift ν)))
    piecewiseLinearNilsequence (D ν).Γ F (fun _ => i) (obs ν) (g ν) (a ν) w
      (alignmentIntegerArrayArgument y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
        (T ν) (p + (F.modulus w : ℤ) * ell) (shift ν) slots) =
      obs ν w (label ν) (alignmentJointNativeCosetEvaluation D n v hv ν slots
        (QuotientGroup.mk (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift
          (fun ν => g ν w (label ν)) (fun ν => a ν w (label ν)) ell))) := by
  let label := fun k =>
    ((((alignmentNaturalBlockProduct x (T k) * x i : ℕ) : ℤ) / (F.gap w i.val : ℤ)),
      alignmentPivotArrayResidue x (T k) (F.modulus w) (x i)
        (alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w (F.modulus w) e x) (shift k)))
  have hr := principal_native_joint_reading_integer_argument D n v hv F q₀ w T y p shift
    (fun k => g k w (label k)) (fun k => a k w (label k)) ell ν slots (obs ν w (label ν))
  rw [alignmentIntegerArrayArgument_progression_quotient y (F.modulus w) (F.modulus w).pos] at hr
  exact (alignment_exposure_frozen_piece_reading (D ν).Γ hF hq hw i C (T ν) hT V U
    hgood hx hy hcut hkey (shift ν) hshift slots hslots p ell hp hdist (obs ν) (g ν) (a ν)).trans hr.symm

end Hindman168
