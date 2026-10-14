import Hindman168.NativeFinitePiPolynomial
import Hindman168.AlignmentExposedNativeSource

/-! The actual heterogeneous finite JOINT exposed source. Components may
have distinct original groups, determining evaluations, bases, vertices and
slot shifts. One genuine product nilmanifold retains all components. -/
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

noncomputable def alignmentJointExposedNativePolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvPolynomial (Sum (Option κ) (Fin N))
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E :=
  nativeFinitePiVectorPolynomial (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (fun ν => alignmentExposedNativeVectorPolynomial (D ν) (n ν) (v ν) (hv ν) (b ν)
      F q₀ w T x (shift ν) (weight ν) (g ν) (a ν))

noncomputable def alignmentJointExposedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    (Sum (Option κ) (Fin N) → ℝ) →
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeFinitePiVectorSource (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    (fun ν => alignmentExposedNativeVectorPolynomial (D ν) (n ν) (v ν) (hv ν) (b ν)
      F q₀ w T x (shift ν) (weight ν) (g ν) (a ν))

theorem alignment_joint_exposed_native_polynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvDegreeLE (alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T x shift weight g a)
      (((s*s+1)^(s+1))*max 1 T.card) := by
  apply native_finite_pi_vector_polynomial_degree
  intro ν
  exact alignment_exposed_native_vector_polynomial_degree (D ν) (n ν) (v ν) (hv ν) (b ν)
    F q₀ w T x (shift ν) (weight ν) (g ν) (a ν)

theorem alignment_joint_exposed_native_source_log
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (z : Sum (Option κ) (Fin N) → ℝ) :
    roughVectorMvEval (alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T x shift weight g a) z =
      nativeLieGlobalLogarithm
        (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
        (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
        (G := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
        (alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z) :=
  native_finite_pi_vector_source_log _ _ z

theorem alignment_joint_exposed_native_source_coordinate
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (z : Sum (Option κ) (Fin N) → ℝ) (ν : ι) :
    nativeFinitePiGroupEquiv (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
      (alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z) ν =
      alignmentExposedNativeSource (D ν) (n ν) (v ν) (hv ν) (b ν)
        F q₀ w T x (shift ν) (weight ν) (g ν) (a ν) z :=
  native_finite_pi_vector_source_coordinate _ _ z ν

theorem alignment_joint_exposed_native_polynomial_frozen
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ w : ℕ) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T y shift weight g a =
      alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T x shift weight g a := by
  unfold alignmentJointExposedNativePolynomial
  apply congrArg (nativeFinitePiVectorPolynomial (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)))
  funext ν
  exact alignment_exposed_native_vector_polynomial_frozen (D ν) (n ν) (v ν) (hv ν) (b ν)
    hF q₀ w T hT hx hy hkey (shift ν) (weight ν) (g ν) (a ν)

theorem alignment_joint_exposed_native_source_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc : κ → ℤ) (weight : ι → κ → ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let actual := fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
      (alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
        T p Y ell inc (weight ν) (shift ν))
    alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z =
      nativeFinitePiGroupValue (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) actual := by
  dsimp only
  apply native_finite_pi_vector_source_samples
  intro ν
  exact alignment_exposed_native_vector_polynomial_actual_eval (D ν) (n ν) (v ν) (hv ν) (b ν)
    hF hq hw T hT hx hy hkey p ell hp inc (weight ν) (shift ν) (g ν) (a ν)

end Hindman168
