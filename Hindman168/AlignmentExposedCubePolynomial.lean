import Hindman168.AlignmentFrozenCubeData
import Hindman168.AlignmentCanonicalCubePolynomial

namespace Hindman168
open scoped BigOperators Classical

noncomputable def alignmentExposedCubePolynomial {n : ℕ} (F : MasterParameterFamily)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (v : AlignmentAddingPair n i → ℤ) :
    MvPolynomial (Option (Option (AlignmentAddingPair n i))) ℚ :=
  letI := alignmentAddingPairFintype n i
  let M : ℕ := F.modulus w
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (M : ℤ)
  let s := alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w M e x) v
  alignmentCubeExponentPolynomial M Y
    (alignmentPivotArrayResidue x T M (x i) 0)
    (alignmentPivotArrayResidue x T M (x i) s) s
    (fun e => if e.targetTail = T then (alignmentIntegerNumerator q₀ w e x : ℚ) else 0)
    (fun e => if e.targetTail = T then (alignmentPairResidue q₀ w M e x : ℚ) else 0)

theorem alignmentExposedCubePolynomial_degree {n : ℕ} (F : MasterParameterFamily)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (v : AlignmentAddingPair n i → ℤ) :
    (alignmentExposedCubePolynomial F q₀ w i T x v).totalDegree ≤ 2 := by
  letI := alignmentAddingPairFintype n i
  exact alignmentCubeExponentPolynomial_degree _ _ _ _ _ _ _

theorem alignmentExposedCubePolynomial_frozen
    {n d : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (q₀ w : ℕ) (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair n i → ℤ) :
    alignmentExposedCubePolynomial F q₀ w i T y v =
      alignmentExposedCubePolynomial F q₀ w i T x v := by
  letI := alignmentAddingPairFintype n i
  have he := alignmentShortExposureKey_rawExposure F w i T h
  have hs := alignmentRawExposure_slot_shift_eq hF q₀ w hx hy he v
  have hq : (fun e : AlignmentAddingPair n i =>
      if e.targetTail = T then (alignmentIntegerNumerator q₀ w e y : ℚ) else 0) =
      (fun e : AlignmentAddingPair n i =>
      if e.targetTail = T then (alignmentIntegerNumerator q₀ w e x : ℚ) else 0) := by
    funext e
    by_cases heT : e.targetTail = T
    · rw [if_pos heT, if_pos heT, alignmentRawExposure_own_numerator_eq q₀ w he e heT]
    · rw [if_neg heT, if_neg heT]
  have hr : (fun e : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w) e y) =
      (fun e : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w) e x) := by
    funext e
    exact (alignmentRawExposure_pairResidue_eq hF q₀ w hx hy he e).symm
  unfold alignmentExposedCubePolynomial
  dsimp only
  rw [← alignmentShortExposureKey_start_eq F w i T h, ← hs,
    alignmentShortExposureKey_arrayResidue_eq F w i T hT h (y i) 0 (Int.ModEq.refl _),
    alignmentShortExposureKey_arrayResidue_eq F w i T hT h (y i) _ (Int.ModEq.refl _), hq]
  have hr' (e : AlignmentAddingPair n i) := congrFun hr e
  simp only [hr']

end Hindman168
