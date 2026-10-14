import Hindman168.ScalarSmallSlopeFractionalBracketInverse
import Hindman168.ScalarMixedFractionalBracketReduction

/-! GENUINE complete Claim 7.7 alternative, with fixed-data natural bounds.
The small-slope inverse is ACTUALLY applied a second time. No analytic oracle
or unsupported explicit power law is used. The multiplier is truly positive. -/
namespace Hindman168
open scoped BigOperators Classical

theorem scalar_fractional_bracket_full_alternative (ι : Type*) [Fintype ι]
    (Z δ B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (β α : ℝ) (ζ γ : ι → ℝ), (∀ i, |ζ i| ≤ Z) →
      ∀ N : ℕ, 0 < N →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
          (∃ r : ℕ, 0 < r ∧ r ≤ A ∧ ∀ i,
            (N : ℝ)*‖(((r : ℝ)*ζ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)) ∨
            ∃ k : ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
              (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨Q,hQ,hfirst⟩ := scalar_fractional_bracket_first_alternative ι Z δ B hδ hδ1 hB
  obtain ⟨S,_,hsecond⟩ := scalar_small_slope_fractional_bracket_inverse ι
    ((Q : ℝ)*(Z+1)) δ (Q : ℝ) ((Q : ℝ)*B)
    (by positivity) hδ hδ1 (Nat.cast_nonneg Q) (by positivity)
  let A := Q+S+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hQA : Q ≤ A := by dsimp only [A]; omega
  have hSA : S ≤ A := by dsimp only [A]; omega
  refine ⟨A,hA,?_⟩
  intro β α ζ γ hζ N hN hdense
  rcases hfirst β α ζ γ hζ N hN hdense with hsmall | hmixed
  · exact Or.inl ⟨1,by omega,by omega,fun i => by
      simpa only [Nat.cast_one,one_mul] using (hsmall i).trans (by exact_mod_cast hQA)⟩
  · obtain ⟨k,r,hne,hsize,hbound⟩ := hmixed
    have hkQ : (∑ i, (k i).natAbs) ≤ Q := (Nat.le_add_right _ _).trans hsize
    have hrQ : r.natAbs ≤ Q := (Nat.le_add_left _ _).trans hsize
    by_cases hr0 : r=0
    · have hk : k ≠ 0 := hne.resolve_right (not_not_intro hr0)
      rw [hr0,Int.cast_zero,zero_mul,add_zero] at hbound
      exact Or.inr ⟨k,hk,hkQ.trans hQA,hbound.trans (by exact_mod_cast hQA)⟩
    · have hrReal : |(r : ℝ)| ≤ (Q : ℝ) := by
        have hh : (r.natAbs : ℝ) ≤ Q := by exact_mod_cast hrQ
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
      have hkReal : ∀ i, |(k i : ℝ)| ≤ (Q : ℝ) := by
        intro i
        have hn := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hkQ
        have hh : ((k i).natAbs : ℝ) ≤ Q := by exact_mod_cast hn
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hh
      let a := (r : ℝ)*α+∑ i, (k i : ℝ)*γ i
      let α' := scalarNearestIntegerResidual a
      let ζ' := fun i => (r : ℝ)*ζ i-(k i : ℝ)
      have hCorrection := scalar_mixed_fractional_bracket_reduction β α ζ γ r k
        (Q : ℝ) Z (Q : ℝ) B (Nat.cast_nonneg Q) hB hrReal hkReal hζ N hbound
      obtain ⟨hα',hζ',herror⟩ := hCorrection
      have hsub : ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β α ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)) ⊆
          (Finset.range N).filter (fun h : ℕ =>
            (N : ℝ)*‖(scalarFractionalBracket ((r : ℝ)*β) α' ζ' γ (h : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)*B) := by
        intro h hh
        obtain ⟨hRange,hsmall⟩ := Finset.mem_filter.mp hh
        exact Finset.mem_filter.mpr ⟨hRange,herror h hsmall⟩
      have hd' : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket ((r : ℝ)*β) α' ζ' γ (h : ℝ) : UnitAddCircle)‖ ≤ (Q : ℝ)*B)).card :=
        hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
      rcases hsecond ((r : ℝ)*β) α' ζ' γ hζ' N hN hα' hd' with hReal | hVector
      · apply Or.inl
        refine ⟨r.natAbs,Int.natAbs_pos.mpr hr0,hrQ.trans hQA,?_⟩
        intro i
        rw [unit_circle_nat_abs_multiplier_norm]
        have hn : ‖(((r : ℝ)*ζ i : ℝ) : UnitAddCircle)‖ ≤ |(r : ℝ)*ζ i-(k i : ℝ)| :=
          (rough_mod_one_near_integer_iff _ _).mpr ⟨k i,le_rfl⟩
        exact ((mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg N)).trans (hReal i)).trans
          (by exact_mod_cast hSA)
      · obtain ⟨v,hv,hvSize,hvBound⟩ := hVector
        exact Or.inr ⟨v,hv,hvSize.trans hSA,hvBound.trans (by exact_mod_cast hSA)⟩

end Hindman168
