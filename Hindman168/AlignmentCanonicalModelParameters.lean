import Hindman168.AlignmentJointCubeParameters
import Hindman168.AlignmentCanonicalCubePolynomial

namespace Hindman168
open scoped BigOperators Classical

theorem alignment_canonical_joint_base_eval
    {κ : Type*} [Fintype κ] {n : ℕ} {i : Fin n}
    (t : Fin n → ℕ) (M : ℕ) (hM : 0 < M)
    (rho : AlignmentAddingPair n i → ℕ) (T : Finset (Fin n))
    (p Y ell : ℤ) (inc weight : κ → ℤ) (v : AlignmentAddingPair n i → ℤ) :
    let tau : ℤ := alignmentNaturalBlockProduct t T
    let s := alignmentIntegerSlotShift rho v
    let r := alignmentPivotArrayResidue t T M p 0
    let rv := alignmentPivotArrayResidue t T M p s
    MvPolynomial.eval (Sum.elim
      (fun j => match j with
        | none => (alignmentCubeBase M tau p Y ell : ℝ)
        | some j => ((tau * inc j : ℤ) : ℝ)) (fun j => (t j : ℝ)))
      (alignmentJointBasePolynomial M Y r rv s weight T) =
        ((alignmentCubeVertex M tau p Y ell inc weight + Y +
          (r + tau * s - rv) / (M : ℤ) : ℤ) : ℝ) := by
  dsimp only
  rw [alignmentJointBasePolynomial_eval]
  have hm : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hk := alignment_cube_residue_correction_exact (M : ℤ)
    (alignmentNaturalBlockProduct t T) p (alignmentIntegerSlotShift rho v) hm
  have h := alignmentCubeBasePolynomial_integral_eval (M : ℤ) Y
    (alignmentPivotArrayResidue t T M p 0)
    (alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift rho v))
    (alignmentIntegerSlotShift rho v)
    (alignmentCubeVertex M (alignmentNaturalBlockProduct t T) p Y ell inc weight)
    (alignmentNaturalBlockProduct t T)
    ((alignmentPivotArrayResidue t T M p 0 +
      (alignmentNaturalBlockProduct t T : ℤ) * alignmentIntegerSlotShift rho v -
      alignmentPivotArrayResidue t T M p (alignmentIntegerSlotShift rho v)) / (M : ℤ)) hm
    (by simpa only [alignmentPivotArrayResidue, add_zero] using hk)
  simpa only [alignmentCubeVertex, alignmentNaturalBlockProduct, Int.cast_add,
    Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_natCast, Nat.cast_prod] using h

theorem alignment_canonical_joint_increment_eval
    {κ : Type*} {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (t : Fin n → ℕ)
    (ht : ∀ j, Nat.Coprime (t j) (primorial w)) {i : Fin n}
    (T : Finset (Fin n)) (z : Option κ → ℝ) (e : AlignmentAddingPair n i) :
    MvPolynomial.eval (Sum.elim z (fun j => (t j : ℝ)))
      (alignmentJointIncrementPolynomial (F.modulus w)
        (if e.targetTail = T then (alignmentIntegerNumerator q₀ w e t : ℝ) else 0)
        (if e.targetTail = T then (alignmentPairResidue q₀ w (F.modulus w) e t : ℝ) else 0) T) =
      ((if e.targetTail = T then alignmentPairProgression q₀ w (F.modulus w) e t else 0 : ℤ) : ℝ) := by
  rw [alignmentJointIncrementPolynomial_eval, alignmentCubeIncrementPolynomial_eval]
  have hm : (F.modulus w : ℝ) ≠ 0 := by exact_mod_cast (F.modulus w).pos.ne'
  by_cases he : e.targetTail = T
  · simp only [if_pos he]
    apply (div_eq_iff hm).mpr
    have hd := alignmentPairProgression_exact hF hq hw t ht e
    rw [he] at hd
    have hdc := congrArg (fun a : ℤ => (a : ℝ)) hd
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast,
      alignmentNaturalBlockProduct, Int.cast_prod, Int.cast_natCast, Nat.cast_prod] at hdc
    exact hdc.symm.trans (mul_comm _ _)
  · simp only [if_neg he, mul_zero, sub_zero, zero_div, Int.cast_zero]

end Hindman168
