import Hindman168.AlignmentCanonicalModelParameters
import Hindman168.AlignmentExposedCubeEvaluation

namespace Hindman168
open scoped BigOperators Classical

noncomputable def alignmentExposedJointBasePolynomial {κ : Type*} [Fintype κ]
    {n : ℕ} (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (x : Fin n → ℕ) (v : AlignmentAddingPair n i → ℤ)
    (weight : κ → ℤ) : MvPolynomial (Sum (Option κ) (Fin n)) ℝ :=
  let M : ℕ := F.modulus w
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ) / (M : ℤ)
  let s := alignmentIntegerSlotShift (fun e => alignmentPairResidue q₀ w M e x) v
  alignmentJointBasePolynomial M Y
    (alignmentPivotArrayResidue x T M (x i) 0)
    (alignmentPivotArrayResidue x T M (x i) s) s weight T

noncomputable def alignmentExposedJointIncrementPolynomial {κ : Type*}
    {n : ℕ} (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (x : Fin n → ℕ) (e : AlignmentAddingPair n i) :
    MvPolynomial (Sum (Option κ) (Fin n)) ℝ :=
  alignmentJointIncrementPolynomial (F.modulus w)
    (if e.targetTail = T then (alignmentIntegerNumerator q₀ w e x : ℝ) else 0)
    (if e.targetTail = T then (alignmentPairResidue q₀ w (F.modulus w) e x : ℝ) else 0) T

theorem alignmentExposedJointBasePolynomial_degree {κ : Type*} [Fintype κ]
    {n : ℕ} (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (x : Fin n → ℕ) (v : AlignmentAddingPair n i → ℤ)
    (weight : κ → ℤ) :
    (alignmentExposedJointBasePolynomial F q₀ w i T x v weight).totalDegree ≤ max 1 T.card :=
  alignmentJointBasePolynomial_degree _ _ _ _ _ _ _

theorem alignmentExposedJointIncrementPolynomial_degree {κ : Type*}
    {n : ℕ} (F : MasterParameterFamily) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (x : Fin n → ℕ) (e : AlignmentAddingPair n i) :
    (alignmentExposedJointIncrementPolynomial (κ := κ) F q₀ w i T x e).totalDegree ≤ T.card :=
  alignmentJointIncrementPolynomial_degree _ _ _ _

theorem alignmentExposedJointBasePolynomial_frozen
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (v : AlignmentAddingPair n i → ℤ) (weight : κ → ℤ) :
    alignmentExposedJointBasePolynomial F q₀ w i T y v weight =
      alignmentExposedJointBasePolynomial F q₀ w i T x v weight := by
  have he := alignmentShortExposureKey_rawExposure F w i T h
  have hs := alignmentRawExposure_slot_shift_eq hF q₀ w hx hy he v
  unfold alignmentExposedJointBasePolynomial
  dsimp only
  rw [← alignmentShortExposureKey_start_eq F w i T h, ← hs,
    alignmentShortExposureKey_arrayResidue_eq F w i T hT h (y i) 0 (Int.ModEq.refl _),
    alignmentShortExposureKey_arrayResidue_eq F w i T hT h (y i) _ (Int.ModEq.refl _)]

theorem alignmentExposedJointIncrementPolynomial_frozen
    {κ : Type*} {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (h : alignmentShortExposureKey F w i T x = alignmentShortExposureKey F w i T y)
    (e : AlignmentAddingPair n i) :
    alignmentExposedJointIncrementPolynomial (κ := κ) F q₀ w i T y e =
      alignmentExposedJointIncrementPolynomial F q₀ w i T x e := by
  have he := alignmentShortExposureKey_rawExposure F w i T h
  unfold alignmentExposedJointIncrementPolynomial
  by_cases heT : e.targetTail = T
  · rw [if_pos heT, if_pos heT, if_pos heT, if_pos heT,
      alignmentRawExposure_own_numerator_eq q₀ w he e heT,
      ← alignmentRawExposure_pairResidue_eq hF q₀ w hx hy he e]
  · simp only [if_neg heT]

end Hindman168
