import Hindman168.AlignmentIntegerSpatialParameters
import Hindman168.SelectedAlignmentJointSourceTransportCRT

/-! Gap-view adapters for the repository's original native source proofs.
The original master conditions and modulus are retained; only the short
exposure key and its bin origin use the separately specified model gap.
No master conditions for the changed-gap view are asserted. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem selected_alignment_exposed_integer_spatial_base_eval {κ : Type*} [Fintype κ]
    {N k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : ℕ)
    (q₀ w : ℕ) (i : Fin N) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (x y : Fin N → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T x=alignmentShortExposureKey (alignmentGeometryWithGap F i.val gap) w i T y)
    (shift : AlignmentAddingPair N i → ℤ) (weight : κ → ℤ) (spatial : Option κ → ℤ) :
    MvPolynomial.eval (Sum.elim (fun j => (spatial j : ℝ)) (fun j => (y j : ℝ)))
      (alignmentExposedJointBasePolynomial (alignmentGeometryWithGap F i.val gap) q₀ w i T x shift weight)=
      (alignmentIntegerSpatialBase (alignmentGeometryWithGap F i.val gap) q₀ w i T y shift weight spatial : ℝ) := by
  rw [←selected_alignmentExposedJointBasePolynomial_frozen hF gap q₀ w i T hT hx hy hkey shift weight]
  exact alignment_joint_integer_spatial_base_eval (alignmentGeometryWithGap F i.val gap) q₀ w i T y shift weight spatial


end Hindman168
