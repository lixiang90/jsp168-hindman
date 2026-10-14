import Hindman168.AlignmentExposedJointParameters
import Hindman168.SelectedAlignmentGeometryView

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open scoped BigOperators Classical

theorem selected_alignmentExposedJointBasePolynomial_frozen
    {κ : Type*} [Fintype κ] {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (h : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (v : AlignmentAddingPair n i → ℤ) (weight : κ → ℤ) :
    alignmentExposedJointBasePolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T y v weight =
      alignmentExposedJointBasePolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x v weight := by
  have he := alignmentShortExposureKey_rawExposure (alignmentGeometryWithGap F i.val gap) w i T h
  have hs := alignmentRawExposure_slot_shift_eq hF q₀ w hx hy he v
  unfold alignmentExposedJointBasePolynomial
  dsimp only
  simp only [alignmentGeometryWithGap_modulus]
  have hr (t : ℤ) := alignmentShortExposureKey_arrayResidue_eq
    (alignmentGeometryWithGap F i.val gap) w i T hT h (y i) t (Int.ModEq.refl _)
  simp only [alignmentGeometryWithGap_modulus] at hr
  rw [← alignmentShortExposureKey_start_eq (alignmentGeometryWithGap F i.val gap) w i T h, ← hs, hr 0, hr _]

theorem selected_alignmentExposedJointIncrementPolynomial_frozen
    {κ : Type*} {n d : ℕ} {A : Finset ℚ}
    {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (gap : ℕ) (q₀ w : ℕ) (i : Fin n)
    (T : Finset (Fin n)) {x y : Fin n → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (h : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x = alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (e : AlignmentAddingPair n i) :
    alignmentExposedJointIncrementPolynomial (κ := κ) (alignmentGeometryWithGap F i.val gap) q₀ w i T y e =
      alignmentExposedJointIncrementPolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x e := by
  have he := alignmentShortExposureKey_rawExposure (alignmentGeometryWithGap F i.val gap) w i T h
  unfold alignmentExposedJointIncrementPolynomial
  simp only [alignmentGeometryWithGap_modulus]
  by_cases heT : e.targetTail = T
  · rw [if_pos heT, if_pos heT, if_pos heT, if_pos heT,
      alignmentRawExposure_own_numerator_eq q₀ w he e heT,
      ← alignmentRawExposure_pairResidue_eq hF q₀ w hx hy he e]
  · simp only [if_neg heT]


end Hindman168
