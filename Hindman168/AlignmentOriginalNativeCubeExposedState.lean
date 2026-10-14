import Hindman168.AlignmentOriginalNativeCubeState
import Hindman168.AlignmentJointExposedNativeSource

/-! The literal original empirical native cube state equals the quotient of
the exposure-fixed joint native logarithmic-polynomial source at EVERY original
integer cube sample. No unsampled extension substitutes for a sampled state. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_original_native_cube_exposed_state
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (ell : Option κ → ℤ) (weight : ι → κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y (ell none) : ℝ)
        | some j => ((tau*ell (some j) : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z : J.G ⧸ J.Γ)=
      alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell := by
  dsimp only
  exact congrArg (fun h => QuotientGroup.mk h)
    (alignment_joint_exposed_native_source_actual_sample D n v hv r b hF hq hw T hT
      hx hy hkey p (ell none) hp (fun j => ell (some j)) weight shift g a)

theorem alignment_original_native_cube_raw_exposed_state
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) (y : Fin N → ℕ)
    (hy : y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support)
    (ell : Option κ → ℤ) (weight : ι → κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) :
    let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
    let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y (ell none) : ℝ)
        | some j => ((tau*ell (some j) : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (alignmentJointExposedNativeSource D n v hv r b F q₀ w T y shift weight g a z : J.G ⧸ J.Γ)=
      alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell := by
  dsimp only
  exact alignment_original_native_cube_exposed_state D n v hv r b hF hq hw T hT
    (alignmentGlobalRawMass_support_coprime F w y hy)
    (alignmentGlobalRawMass_support_coprime F w y hy) rfl
    _ (alignmentMicrocellFirst_modEq _ _ _) ell weight shift g a

end Hindman168
