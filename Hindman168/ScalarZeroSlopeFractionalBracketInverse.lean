import Hindman168.UnitTorusOptionZeroSlopeBracketInverse
import Mathlib.Logic.Equiv.Option

/-! GENUINE zero-slope bracket inverse for ANY actual finite index type.
The maximal coordinate is selected and reindexed, with true nonzero integer
frequency/size/dot-product transport and ALL budgets before all raw inputs. -/
namespace Hindman168
open scoped BigOperators Classical

theorem scalar_zero_slope_fractional_bracket_inverse (ι : Type*) [Fintype ι]
    (Z δ B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (β : ℝ) (ζ γ : ι → ℝ), (∀ i, |ζ i| ≤ Z) →
      ∀ N : ℕ, 0 < N →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
          (N : ℝ)*‖(scalarFractionalBracket β 0 ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
          (∀ i, (N : ℝ)*|ζ i| ≤ (A : ℝ)) ∨
            ∃ k : ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
              (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  have hfamily := fun i : ι => unit_torus_option_zero_slope_bracket_inverse {j : ι // j ≠ i} Z δ B hZ hδ hδ1 hB
  choose A hA hInv using hfamily
  let Q := 1+∑ i, A i
  have hQ : 0 < Q := by dsimp only [Q]; omega
  have hAQ : ∀ i, A i ≤ Q := by
    intro i
    have hi : A i ≤ ∑ j, A j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp only [Q]
    omega
  refine ⟨Q,hQ,?_⟩
  intro β ζ γ hζ N hN hdense
  by_cases hz : ζ=0
  · exact Or.inl (fun i => by simp only [hz,Pi.zero_apply,abs_zero,mul_zero]; exact Nat.cast_nonneg Q)
  · have hnonempty : (Finset.univ : Finset ι).Nonempty := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
      exact ⟨i,Finset.mem_univ i⟩
    obtain ⟨i,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι) (fun j => |ζ j|) hnonempty
    let e := Equiv.optionSubtypeNe i
    let ζ' := fun o : Option {j : ι // j ≠ i} => ζ (e o)
    let γ' := fun o : Option {j : ι // j ≠ i} => γ (e o)
    have he : ∀ h : ℝ, scalarFractionalBracket β 0 ζ' γ' h=scalarFractionalBracket β 0 ζ γ h := by
      intro h
      dsimp only [scalarFractionalBracket,ζ',γ']
      rw [e.sum_comp (fun j => ζ j*Int.fract (h*γ j))]
    have hd' : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
        (N : ℝ)*‖(scalarFractionalBracket β 0 ζ' γ' (h : ℝ) : UnitAddCircle)‖ ≤ B)).card := by
      simp_rw [he]
      exact hdense
    have hmax' : ∀ o, |ζ' o| ≤ |ζ' none| := by
      intro o
      change |ζ (e o)| ≤ |ζ (e none)|
      rw [show e none=i from rfl]
      exact hmax (e o) (Finset.mem_univ _)
    rcases hInv i β ζ' γ' (fun o => hζ (e o)) hmax' N hN hd' with hsmall | hvector
    · apply Or.inl
      intro j
      have hj := hsmall (e.symm j)
      change (N : ℝ)*|ζ (e (e.symm j))| ≤ (A i : ℝ) at hj
      rw [e.apply_symm_apply] at hj
      exact hj.trans (by exact_mod_cast hAQ i)
    · obtain ⟨k',hk',hsize,hbound⟩ := hvector
      let k := fun j : ι => k' (e.symm j)
      have hk : k ≠ 0 := by
        intro hzero
        apply hk'
        funext o
        have hj := congrFun hzero (e o)
        simpa only [k,e.symm_apply_apply,Pi.zero_apply] using hj
      have hsizeEq : (∑ j, (k j).natAbs)=∑ o, (k' o).natAbs := by
        have hh := e.sum_comp (fun j => (k j).natAbs)
        simpa only [k,e.symm_apply_apply] using hh.symm
      have hphaseEq : (∑ j, (k j : ℝ)*γ j)=∑ o, (k' o : ℝ)*γ' o := by
        have hh := e.sum_comp (fun j => (k j : ℝ)*γ j)
        simpa only [k,γ',e.symm_apply_apply] using hh.symm
      exact Or.inr ⟨k,hk,by rw [hsizeEq]; exact hsize.trans (hAQ i),
        by rw [hphaseEq]; exact hbound.trans (by exact_mod_cast hAQ i)⟩

end Hindman168
