import Hindman168.AlignmentExposedJointParameters

namespace Hindman168
open scoped BigOperators Classical

theorem alignmentExposedJointBasePolynomial_eval
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v : AlignmentAddingPair n i → ℤ) :
    let M : ℕ := F.modulus w
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (M : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let rho := fun e => alignmentPairResidue q₀ w M e y
    let s := alignmentIntegerSlotShift rho v
    let r := alignmentPivotArrayResidue y T M p 0
    let rv := alignmentPivotArrayResidue y T M p s
    MvPolynomial.eval (Sum.elim
      (fun j => match j with
        | none => (alignmentCubeBase M tau p Y ell : ℝ)
        | some j => ((tau * inc j : ℤ) : ℝ)) (fun j => (y j : ℝ)))
      (alignmentExposedJointBasePolynomial F q₀ w i T x v weight) =
        ((alignmentCubeVertex M tau p Y ell inc weight + Y +
          (r + tau * s - rv) / (M : ℤ) : ℤ) : ℝ) := by
  dsimp only
  have hc := alignment_canonical_joint_base_eval y (F.modulus w) (F.modulus w).pos
    (fun e => alignmentPairResidue q₀ w (F.modulus w) e y) T p
    ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) ell inc weight v
  dsimp only at hc
  have hr (s : ℤ) : alignmentPivotArrayResidue y T (F.modulus w) p s =
      alignmentPivotArrayResidue y T (F.modulus w) (y i) s :=
    Int.ModEq.mul_left _ (hp.add_right s)
  rw [← alignmentExposedJointBasePolynomial_frozen hF q₀ w i T hT hx hy hkey v weight]
  unfold alignmentExposedJointBasePolynomial
  dsimp only
  rw [← alignmentShortExposureKey_start_eq F w i T hkey]
  rw [hr 0, hr _] at hc ⊢
  exact hc

theorem alignmentExposedJointIncrementPolynomial_eval
    {κ : Type*} {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (i : Fin n)
    (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (z : Option κ → ℝ) (e : AlignmentAddingPair n i) :
    MvPolynomial.eval (Sum.elim z (fun j => (y j : ℝ)))
      (alignmentExposedJointIncrementPolynomial F q₀ w i T x e) =
        ((if e.targetTail = T then alignmentPairProgression q₀ w (F.modulus w) e y else 0 : ℤ) : ℝ) := by
  rw [← alignmentExposedJointIncrementPolynomial_frozen hF q₀ w i T hx hy hkey e]
  exact alignment_canonical_joint_increment_eval hF hq hw y hy T z e

end Hindman168
