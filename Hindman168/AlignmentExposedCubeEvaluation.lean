import Hindman168.AlignmentExposedCubePolynomial

namespace Hindman168
open scoped BigOperators Classical

theorem alignmentExposedCubePolynomial_eval
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) {q₀ w : ℕ}
    (hq : 0 < q₀) (hw : q₀ + 1 ≤ w) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc weight : κ → ℤ) (v u : AlignmentAddingPair n i → ℤ) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)
    let X := alignmentCubeVertex (F.modulus w) (alignmentNaturalBlockProduct y T) p Y ell inc weight
    MvPolynomial.eval (fun z => match z with
      | none => (X : ℚ)
      | some none => (alignmentNaturalBlockProduct y T : ℚ)
      | some (some e) => (u e : ℚ))
      (alignmentExposedCubePolynomial F q₀ w i T x v) =
      ((alignmentIntegerArrayArgument y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
        (p + (F.modulus w : ℤ) * (ell + ∑ j, weight j * inc j)) v u /
          (F.modulus w : ℤ) : ℤ) : ℚ) := by
  letI := alignmentAddingPairFintype n i
  have hc := alignment_canonical_cube_polynomial hF hq hw y hy T p
    ((alignmentShortBinStart F w i T x : ℤ) / (F.modulus w : ℤ)) ell inc weight v u
  dsimp only at hc ⊢
  have hr (s : ℤ) : alignmentPivotArrayResidue y T (F.modulus w) p s =
      alignmentPivotArrayResidue y T (F.modulus w) (y i) s := by
    exact Int.ModEq.mul_left _ (hp.add_right s)
  rw [hr 0, hr _] at hc
  rw [← alignmentExposedCubePolynomial_frozen hF q₀ w i T hT hx hy hkey v]
  unfold alignmentExposedCubePolynomial
  dsimp only
  rw [← alignmentShortExposureKey_start_eq F w i T hkey]
  simp only [Int.cast_natCast] at hc
  convert hc using 1
  congr 1

end Hindman168
