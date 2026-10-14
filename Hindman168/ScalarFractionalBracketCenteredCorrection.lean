import Hindman168.ScalarFractionalBracket
import Hindman168.IntegerWeightedModOneNorm

/-! The alpha correction in Claim 7.7 uses a TRUE nearest-integer residual.
The [0,1) fractional part is never assumed absolutely small from circle norm. -/
namespace Hindman168
open scoped BigOperators Classical

noncomputable def scalarNearestIntegerResidual (x : ℝ) : ℝ := x-(round x : ℝ)

theorem scalar_nearest_integer_residual_abs (x : ℝ) :
    |scalarNearestIntegerResidual x|=‖(x : UnitAddCircle)‖ := UnitAddCircle.norm_eq.symm

theorem scalar_nearest_integer_residual_circle (x : ℝ) :
    (scalarNearestIntegerResidual x : UnitAddCircle)=(x : UnitAddCircle) := by
  have hz : ((round x : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x,by simp⟩
  rw [scalarNearestIntegerResidual,AddCircle.coe_sub,hz,sub_zero]

theorem scalar_fractional_bracket_integer_correction {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (r : ℤ) (k : ι → ℤ) (h : ℕ) :
    let a := (r : ℝ)*α+∑ i, (k i : ℝ)*γ i
    (scalarFractionalBracket ((r : ℝ)*β) (scalarNearestIntegerResidual a)
      (fun i => (r : ℝ)*ζ i-(k i : ℝ)) γ (h : ℝ) : UnitAddCircle) =
        (((r : ℝ)*scalarFractionalBracket β α ζ γ (h : ℝ) : ℝ) : UnitAddCircle) := by
  intro a
  let z : ℤ := -(h : ℤ)*round a+∑ i, k i*⌊(h : ℝ)*γ i⌋
  have he : scalarFractionalBracket ((r : ℝ)*β) (scalarNearestIntegerResidual a)
      (fun i => (r : ℝ)*ζ i-(k i : ℝ)) γ (h : ℝ) =
        (r : ℝ)*scalarFractionalBracket β α ζ γ (h : ℝ)+(z : ℝ) := by
    have hs : (∑ i, (k i : ℝ)*Int.fract ((h : ℝ)*γ i)) =
        (h : ℝ)*(∑ i, (k i : ℝ)*γ i)-∑ i, (k i : ℝ)*(⌊(h : ℝ)*γ i⌋ : ℝ) := by
      simp_rw [Int.fract,mul_sub]
      rw [Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hr : (∑ i, (r : ℝ)*ζ i*Int.fract ((h : ℝ)*γ i)) =
        (r : ℝ)*∑ i, ζ i*Int.fract ((h : ℝ)*γ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp only [scalarFractionalBracket,scalarNearestIntegerResidual,z,a]
    push_cast
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,hs,hr]
    ring
  rw [he,AddCircle.coe_add]
  have hz : ((z : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z,by simp⟩
  rw [hz,add_zero]

theorem scalar_fractional_bracket_corrected_error {ι : Type*} [Fintype ι]
    (β α : ℝ) (ζ γ : ι → ℝ) (r : ℤ) (k : ι → ℤ) (h N : ℕ) (B : ℝ)
    (hsmall : (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B) :
    let a := (r : ℝ)*α+∑ i, (k i : ℝ)*γ i
    (N : ℝ)*‖(scalarFractionalBracket ((r : ℝ)*β) (scalarNearestIntegerResidual a)
      (fun i => (r : ℝ)*ζ i-(k i : ℝ)) γ (h : ℝ) : UnitAddCircle)‖ ≤ |(r : ℝ)| * B := by
  intro a
  rw [scalar_fractional_bracket_integer_correction]
  have hm := integer_weighted_mod_one_norm_bound (Finset.univ : Finset Unit)
    (fun _ => r) (fun _ => scalarFractionalBracket β α ζ γ (h : ℝ))
  have hm' : ‖(((r : ℝ)*scalarFractionalBracket β α ζ γ (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤
      |(r : ℝ)| * ‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ := by
    simpa only [Finset.univ_unique,Finset.sum_singleton] using hm
  calc
    _ ≤ (N : ℝ)*(|(r : ℝ)| * ‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖) :=
      mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg N)
    _ = |(r : ℝ)| * ((N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (abs_nonneg _)

end Hindman168
