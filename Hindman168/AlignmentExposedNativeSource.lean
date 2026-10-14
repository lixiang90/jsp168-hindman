import Hindman168.AlignmentExposedNativeVectorPolynomial

/-! The all-real native source constructed from the ACTUAL exposed vector
polynomial. Its values at genuine cube samples are proved equal to the
original group array, so extension values cannot replace the sampled source. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : NativeNilmanifoldData.{u} s) (n : ℕ)
  (v : Fin (n+1) → AlignmentAddingPair N i → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))
  {r : ℕ} (b : Basis (Fin r) ℝ (alignmentNativeArrayData D n v hv).E)


noncomputable def alignmentExposedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    (Sum (Option κ) (Fin N) → ℝ) → (alignmentNativeArrayData D n v hv).G :=
  nativeVectorPolynomialSource (alignmentNativeArrayData D n v hv)
    (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a)

theorem alignment_exposed_native_source_log
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G)
    (z : Sum (Option κ) (Fin N) → ℝ) :
    roughVectorMvEval (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a) z =
      nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G)
        (alignmentExposedNativeSource D n v hv b F q₀ w T x shift weight g a z) :=
  (native_vector_polynomial_source_log (alignmentNativeArrayData D n v hv) _ z).symm

theorem alignment_exposed_native_source_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (shift : AlignmentAddingPair N i → ℤ) (g a : D.G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let actual := alignmentNativeArrayDataValue D n v hv (alignmentNativeCanonicalCubeArray n v hv g a y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
      T p Y ell inc weight shift)
    alignmentExposedNativeSource D n v hv b F q₀ w T x shift weight g a z=actual := by
  dsimp only
  apply native_vector_polynomial_source_sample
  exact alignment_exposed_native_vector_polynomial_actual_eval D n v hv b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a

end Hindman168
