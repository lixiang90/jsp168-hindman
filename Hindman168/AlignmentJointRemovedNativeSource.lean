import Hindman168.AlignmentJointExposedNativeSource
import Hindman168.RoughRemovedFactorPolynomial

/-! The genuine finite JOINT source with only the removed factor free.
All components and every spatial variable survive. Normalized residue
packets and ORIGINAL simultaneous sampled-array equality are proved. -/
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


noncomputable def alignmentJointRemovedNativePolynomial
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvPolynomial (Option (Option κ)) (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E :=
  roughRemovedFactorPolynomial j frozen
    (alignmentJointExposedNativePolynomial D n v hv r b F q₀ w T x shift weight g a)

noncomputable def alignmentJointRemovedNativeSource
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    (Option (Option κ) → ℝ) → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  nativeVectorPolynomialSource (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)))
    (alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a)

theorem alignment_joint_removed_native_polynomial_degree
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    RoughVectorMvDegreeLE
      (alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a)
      (((s*s+1)^(s+1))*max 1 T.card) :=
  rough_removed_factor_polynomial_degree j frozen
    (alignment_joint_exposed_native_polynomial_degree D n v hv r b F q₀ w T x shift weight g a)

theorem alignment_joint_removed_native_source_frozen_update
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ) (z : ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G) :
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j (Function.update frozen j z) shift weight g a =
      alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a := by
  unfold alignmentJointRemovedNativeSource alignmentJointRemovedNativePolynomial
  rw [rough_removed_factor_polynomial_frozen_update]

theorem alignment_joint_removed_native_residual_packet
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (j : Fin N) (frozen : Fin N → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (residue : Option κ → ℤ) (q : ℕ) :
    let p := alignmentJointRemovedNativePolynomial D n v hv r b F q₀ w T x j frozen shift weight g a
    let Q := alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j frozen shift weight g a
    RoughVectorMvDegreeLE (roughNativeResidualPolynomial p residue q)
      (((s*s+1)^(s+1))*max 1 T.card) ∧
    ∀ (z : ℝ) (y : Option κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p residue q) (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
          (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I) (G := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
          (roughNativeResidualSource (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) Q residue q (Option.elim · z y)) := by
  dsimp only
  constructor
  · exact rough_native_residual_polynomial_degree
      (alignment_joint_removed_native_polynomial_degree D n v hv r b F q₀ w T x j frozen shift weight g a) residue q
  · exact native_vector_polynomial_residual_log (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) _ residue q

theorem alignment_joint_removed_native_source_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (j : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc : κ → ℤ) (weight : ι → κ → ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z :=
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ))
    let actual := fun ν => alignmentNativeArrayDataValue (D ν) (n ν) (v ν) (hv ν)
      (alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y)
        T p Y ell inc (weight ν) (shift ν))
    alignmentJointRemovedNativeSource D n v hv r b F q₀ w T x j (fun k => (y k : ℝ)) shift weight g a
      (Option.elim · (y j : ℝ) z) =
      nativeFinitePiGroupValue (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) actual := by
  dsimp only
  apply native_vector_polynomial_source_sample
  rw [alignmentJointRemovedNativePolynomial,rough_removed_factor_polynomial_eval,Function.update_eq_self]
  have he := alignment_joint_exposed_native_source_actual_sample D n v hv r b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift g a
  have hlog := alignment_joint_exposed_native_source_log D n v hv r b F q₀ w T x shift weight g a
    (Sum.elim (fun z : Option κ => match z with
      | none => (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct y T) p
          ((alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)) ell : ℝ)
      | some z => (((alignmentNaturalBlockProduct y T : ℤ)*inc z : ℤ) : ℝ))
      (fun z : Fin N => (y z : ℝ)))
  exact hlog.trans (congrArg
    (nativeLieGlobalLogarithm (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I) (G := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)) he)

end Hindman168
