import Hindman168.AlignmentExposedNativeSource
import Hindman168.RoughRemovedFactorPolynomial

/-! The actual exposed source with ONE factor free and all other factors
frozen. The native polynomial/log residual packet is constructed outright;
sample equality still refers to the original actual cube array. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : NativeNilmanifoldData.{u} s) (n : ℕ)
  (v : Fin (n+1) → AlignmentAddingPair N i → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))
  {r : ℕ} (b : Basis (Fin r) ℝ (alignmentNativeArrayData D n v hv).E)



noncomputable def alignmentRemovedNativePolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    RoughVectorMvPolynomial (Option (Option κ)) (alignmentNativeArrayData D n v hv).E :=
  roughRemovedFactorPolynomial j frozen
    (alignmentExposedNativeVectorPolynomial D n v hv b F q₀ w T x shift weight g a)

noncomputable def alignmentRemovedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    (Option (Option κ) → ℝ) → (alignmentNativeArrayData D n v hv).G :=
  nativeVectorPolynomialSource (alignmentNativeArrayData D n v hv)
    (alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a)

theorem alignment_removed_native_polynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    RoughVectorMvDegreeLE
      (alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a)
      (((s*s+1)^(s+1))*max 1 T.card) :=
  rough_removed_factor_polynomial_degree j frozen
    (alignment_exposed_native_vector_polynomial_degree D n v hv b F q₀ w T x shift weight g a)

theorem alignment_removed_native_source_frozen_update
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ) (z : ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G) :
    alignmentRemovedNativeSource D n v hv b F q₀ w T x j (Function.update frozen j z) shift weight g a =
      alignmentRemovedNativeSource D n v hv b F q₀ w T x j frozen shift weight g a := by
  unfold alignmentRemovedNativeSource alignmentRemovedNativePolynomial
  rw [rough_removed_factor_polynomial_frozen_update]

theorem alignment_removed_native_residual_packet
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (g a : D.G)
    (residue : Option κ → ℤ) (q : ℕ) :
    let p := alignmentRemovedNativePolynomial D n v hv b F q₀ w T x j frozen shift weight g a
    let Q := alignmentRemovedNativeSource D n v hv b F q₀ w T x j frozen shift weight g a
    RoughVectorMvDegreeLE (roughNativeResidualPolynomial p residue q)
      (((s*s+1)^(s+1))*max 1 T.card) ∧
    ∀ (z : ℝ) (y : Option κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p residue q) (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
          (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G)
          (roughNativeResidualSource (alignmentNativeArrayData D n v hv) Q residue q (Option.elim · z y)) := by
  dsimp only
  constructor
  · exact rough_native_residual_polynomial_degree
      (alignment_removed_native_polynomial_degree D n v hv b F q₀ w T x j frozen shift weight g a) residue q
  · exact native_vector_polynomial_residual_log (alignmentNativeArrayData D n v hv) _ residue q

theorem alignment_removed_native_source_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (j : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (shift : AlignmentAddingPair N i → ℤ) (g a : D.G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z :=
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ))
    let actual := alignmentNativeArrayDataValue D n v hv (alignmentNativeCanonicalCubeArray n v hv g a y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
      T p Y ell inc weight shift)
    alignmentRemovedNativeSource D n v hv b F q₀ w T x j (fun k => (y k : ℝ)) shift weight g a
      (Option.elim · (y j : ℝ) z)=actual := by
  dsimp only
  apply native_vector_polynomial_source_sample
  rw [alignmentRemovedNativePolynomial,rough_removed_factor_polynomial_eval,Function.update_eq_self]
  exact alignment_exposed_native_vector_polynomial_actual_eval D n v hv b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a

end Hindman168
