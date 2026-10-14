import Hindman168.ScalarZeroSlopeFractionalBracketInverse
import Hindman168.ScalarFractionalBracketAugmentation

/-! GENUINE FIRST quantitative alternative in Claim 7.7, for unrestricted
alpha. Zero-slope inverse is actually applied to the augmented frequency;
no quantitative bracket lemma is supplied as a hypothesis. -/
namespace Hindman168
open scoped BigOperators Classical

theorem scalar_fractional_bracket_first_alternative (ι : Type*) [Fintype ι]
    (Z δ B : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (β α : ℝ) (ζ γ : ι → ℝ), (∀ i, |ζ i| ≤ Z) →
      ∀ N : ℕ, 0 < N →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
          (∀ i, (N : ℝ)*‖(ζ i : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
            ∃ (k : ι → ℤ) (r : ℤ), (k ≠ 0 ∨ r ≠ 0) ∧
              (∑ i, (k i).natAbs)+r.natAbs ≤ A ∧
              (N : ℝ)*‖(((∑ i, (k i : ℝ)*γ i)+(r : ℝ)*α : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A,hA,hinv⟩ := scalar_zero_slope_fractional_bracket_inverse (Option ι) (max Z 1) δ B
    (le_trans zero_le_one (le_max_right _ _)) hδ hδ1 hB
  refine ⟨A,hA,?_⟩
  intro β α ζ γ hζ N hN hdense
  let ζ' := fun o : Option ι => o.elim 1 ζ
  let γ' := fun o : Option ι => o.elim α γ
  have hd' : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(scalarFractionalBracket β 0 ζ' γ' (h : ℝ) : UnitAddCircle)‖ ≤ B)).card := by
    simp_rw [show ∀ h : ℝ, (scalarFractionalBracket β 0 ζ' γ' h : UnitAddCircle)=
      (scalarFractionalBracket β α ζ γ h : UnitAddCircle) from
        scalar_fractional_bracket_augmentation_circle β α ζ γ]
    exact hdense
  rcases hinv β ζ' γ' (scalar_fractional_bracket_augmented_coefficient_bound ζ Z hζ) N hN hd' with hsmall | hvector
  · apply Or.inl
    intro i
    have hn : ‖(ζ i : UnitAddCircle)‖ ≤ |ζ i| :=
      (rough_mod_one_near_integer_iff _ _).mpr ⟨0,by simp⟩
    exact (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg N)).trans (hsmall (some i))
  · obtain ⟨v,hv,hsize,hbound⟩ := hvector
    let k := fun i => v (some i)
    let r := v none
    have hnonzero : k ≠ 0 ∨ r ≠ 0 := by
      by_contra! h
      apply hv
      funext o
      cases o with
      | none => exact h.2
      | some i => exact congrFun h.1 i
    have hsize' : (∑ i, (k i).natAbs)+r.natAbs=∑ o, (v o).natAbs := by
      rw [Fintype.sum_option]
      exact Nat.add_comm _ _
    have he : (∑ o, (v o : ℝ)*γ' o)=(∑ i, (k i : ℝ)*γ i)+(r : ℝ)*α := by
      rw [Fintype.sum_option]
      change (r : ℝ)*α+(∑ i, (k i : ℝ)*γ i)=_
      ring
    exact Or.inr ⟨k,r,hnonzero,by rw [hsize']; exact hsize,by rw [← he]; exact hbound⟩

end Hindman168
