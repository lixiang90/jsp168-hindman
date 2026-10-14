import Hindman168.AlignmentExposedJointEvaluation
import Hindman168.SelectedAlignmentJointSourceTransportArithmetic

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open scoped BigOperators Classical

theorem selected_alignmentExposedJointBasePolynomial_eval
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v : AlignmentAddingPair n i → ℤ) :
    let M : ℕ := F.modulus w
    let Y : ℤ := (alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ) / (M : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let rho := fun e => alignmentPairResidue q₀ w M e y
    let s := alignmentIntegerSlotShift rho v
    let r := alignmentPivotArrayResidue y T M p 0
    let rv := alignmentPivotArrayResidue y T M p s
    MvPolynomial.eval (Sum.elim
      (fun j => match j with
        | none => (alignmentCubeBase M tau p Y ell : ℝ)
        | some j => ((tau * inc j : ℤ) : ℝ)) (fun j => (y j : ℝ)))
      (alignmentExposedJointBasePolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x v weight) =
        ((alignmentCubeVertex M tau p Y ell inc weight + Y +
          (r + tau * s - rv) / (M : ℤ) : ℤ) : ℝ) := by
  dsimp only
  have hc := alignment_canonical_joint_base_eval y (F.modulus w) (F.modulus w).pos
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) T p
    ((alignmentShortBinStart (alignmentGeometryWithGap F i.val gap) w i T x : ℤ) / (F.modulus w : ℤ)) ell inc weight v
  dsimp only at hc
  have hr (s : ℤ) : alignmentPivotArrayResidue y T (F.modulus w) p s =
      alignmentPivotArrayResidue y T (F.modulus w) (y i) s :=
    Int.ModEq.mul_left _ (hp.add_right s)
  rw [← selected_alignmentExposedJointBasePolynomial_frozen hF gap q₀ w i T hT hx hy hkey v weight]
  unfold alignmentExposedJointBasePolynomial
  dsimp only
  rw [← alignmentShortExposureKey_start_eq (alignmentGeometryWithGap F i.val gap) w i T hkey]
  rw [hr 0, hr _] at hc ⊢
  exact hc

theorem selected_alignmentExposedJointIncrementPolynomial_eval
    {κ : Type*} {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (i : Fin n)
    (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (z : Option κ → ℝ) (e : AlignmentAddingPair n i) :
    MvPolynomial.eval (Sum.elim z (fun j => (y j : ℝ)))
      (alignmentExposedJointIncrementPolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x e) =
        ((if e.targetTail = T then alignmentPairProgression q₀ w (F.modulus w) e y else 0 : ℤ) : ℝ) := by
  rw [← selected_alignmentExposedJointIncrementPolynomial_frozen hF gap q₀ w i T hx hy hkey e]
  exact alignment_canonical_joint_increment_eval hF hq hw y hy T z e


end Hindman168
