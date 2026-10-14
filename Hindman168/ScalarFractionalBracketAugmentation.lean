import Hindman168.ScalarFractionalBracketCenteredCorrection

/-! The FIRST use of Proposition 5.3 in Claim 7.7: adjoin the unrestricted
alpha frequency, with coefficient one and actual zero linear slope. -/
namespace Hindman168
open scoped BigOperators

theorem scalar_fractional_bracket_augmentation {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (h : ℝ) :
    scalarFractionalBracket β 0 (fun o : Option ι => o.elim 1 ζ)
      (fun o : Option ι => o.elim α γ) h =
        scalarFractionalBracket β α ζ γ h-(⌊h*α⌋ : ℝ) := by
  simp only [scalarFractionalBracket,Fintype.sum_option,Option.elim_none,Option.elim_some,
    zero_mul,one_mul,Int.fract]
  ring

theorem scalar_fractional_bracket_augmentation_circle {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (h : ℝ) :
    (scalarFractionalBracket β 0 (fun o : Option ι => o.elim 1 ζ)
      (fun o : Option ι => o.elim α γ) h : UnitAddCircle) =
        (scalarFractionalBracket β α ζ γ h : UnitAddCircle) := by
  rw [scalar_fractional_bracket_augmentation,AddCircle.coe_sub]
  have hz : ((⌊h*α⌋ : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨⌊h*α⌋,by simp⟩
  rw [hz,sub_zero]

theorem scalar_fractional_bracket_augmented_coefficient_bound {ι : Type*}
    (ζ : ι → ℝ) (Z : ℝ) (hZ : ∀ i, |ζ i| ≤ Z) :
    ∀ o : Option ι, |o.elim 1 ζ| ≤ max Z 1 := by
  intro o
  cases o with
  | none => simpa only [Option.elim_none,abs_one] using le_max_right Z 1
  | some i => exact (hZ i).trans (le_max_left Z 1)

end Hindman168
