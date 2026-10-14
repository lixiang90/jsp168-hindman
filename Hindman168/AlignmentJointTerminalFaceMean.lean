import Hindman168.AlignmentJointIntegerFaceTranslation
import Hindman168.AlignmentJointTerminalGridMeans

/-! The actual terminal d-grid with a spatial Delta shift is EXACTLY its
unshifted law tested by the original product slot automorphism. Same original
box, choice, normalization, exposed anchor and supported tail tuple. -/
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

theorem alignment_joint_terminal_denominator_face_mean
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (d : ℕ) (choice lo hi : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T)
    (obs : ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) → ℂ) :
    alignmentJointTranslatedDenominatorMean D n v hv r b F q₀ w T x d choice shift weight g a
      (fun k : T => y k.val) lo hi
      (fun k => if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0) obs=
      alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a
        (fun k : T => y k.val) lo hi
        (obs ∘ alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))) := by
  unfold alignmentJointTranslatedDenominatorMean alignmentJointDenominatorSpatialMean
  congr 1
  funext z
  exact congrArg obs (alignment_joint_tail_integer_coset_own_pair_translation D n v hv r b
    hF hq hw T hT hx hy hkey shift weight g a z j e he).symm

end Hindman168
