import Hindman168.AlignmentCubeExponentPolynomial

namespace Hindman168
open scoped BigOperators Classical

theorem alignment_canonical_cube_polynomial
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (t : Fin n → ℕ)
    (ht : ∀ j, Nat.Coprime (t j) (primorial w)) {i : Fin n}
    (T : Finset (Fin n)) (p Y ell : ℤ) (inc weight : κ → ℤ)
    (v u : AlignmentAddingPair n i → ℤ) :
    letI := alignmentAddingPairFintype n i
    let M : ℕ := F.modulus w
    let tau : ℤ := alignmentNaturalBlockProduct t T
    let rho := fun e => alignmentPairResidue q₀ w M e t
    let delta := fun e => alignmentPairProgression q₀ w M e t
    let s := alignmentIntegerSlotShift rho v
    let r := alignmentPivotArrayResidue t T M p 0
    let rv := alignmentPivotArrayResidue t T M p s
    let x := alignmentCubeVertex M tau p Y ell inc weight
    MvPolynomial.eval (fun z => match z with
      | none => (x : ℚ)
      | some none => (tau : ℚ)
      | some (some e) => (u e : ℚ))
      (alignmentCubeExponentPolynomial M Y r rv s
        (fun e => if e.targetTail = T then (alignmentIntegerNumerator q₀ w e t : ℚ) else 0)
        (fun e => if e.targetTail = T then (rho e : ℚ) else 0)) =
      ((alignmentIntegerArrayArgument t M rho delta T
        (p + (M : ℤ) * (ell + ∑ j, weight j * inc j)) v u / (M : ℤ) : ℤ) : ℚ) := by
  letI := alignmentAddingPairFintype n i
  dsimp only
  have hm : (F.modulus w : ℤ) ≠ 0 := by exact_mod_cast (F.modulus w).pos.ne'
  let rho := fun e : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w) e t
  let delta := fun e : AlignmentAddingPair n i => alignmentPairProgression q₀ w (F.modulus w) e t
  let s := alignmentIntegerSlotShift rho v
  let r := alignmentPivotArrayResidue t T (F.modulus w) p 0
  let rv := alignmentPivotArrayResidue t T (F.modulus w) p s
  let tau : ℤ := alignmentNaturalBlockProduct t T
  have hk : (F.modulus w : ℤ) * ((r + tau * s - rv) / (F.modulus w : ℤ)) =
      r + tau * s - rv := by
    simpa only [r, rv, alignmentPivotArrayResidue, add_zero, tau] using
      alignment_cube_residue_correction_exact (F.modulus w) tau p s hm
  have hd (e : AlignmentAddingPair n i) :
      (F.modulus w : ℤ) * (if e.targetTail = T then delta e else 0) =
        (if e.targetTail = T then (alignmentIntegerNumerator q₀ w e t : ℤ) else 0) -
          tau * (if e.targetTail = T then (rho e : ℤ) else 0) := by
    by_cases he : e.targetTail = T
    · simpa only [if_pos he, delta, rho, tau, he, if_true] using
        alignmentPairProgression_exact hF hq hw t ht e
    · simp only [if_neg he, mul_zero, sub_zero]
  have hp := alignmentCubeExponentPolynomial_integral_eval (F.modulus w) Y r rv s
    (alignmentCubeVertex (F.modulus w) tau p Y ell inc weight) tau
    ((r + tau * s - rv) / (F.modulus w : ℤ)) hm
    (fun e => if e.targetTail = T then (alignmentIntegerNumerator q₀ w e t : ℤ) else 0)
    (fun e => if e.targetTail = T then (rho e : ℤ) else 0) u
    (fun e => if e.targetTail = T then delta e else 0) hk hd
  rw [alignmentIntegerArrayArgument_cube_quotient t (F.modulus w) (F.modulus w).pos
    (Y := Y)]
  simp only [Int.cast_ite, Int.cast_natCast, Int.cast_zero, mul_ite, mul_zero,
    alignmentIntegerArrayProgression, rho, delta, tau, s, r, rv] at hp ⊢
  convert hp using 1
  congr 1
  congr 1
  funext z
  cases z with
  | none => rfl
  | some z =>
    cases z with
    | none => rfl
    | some e => rfl

end Hindman168
