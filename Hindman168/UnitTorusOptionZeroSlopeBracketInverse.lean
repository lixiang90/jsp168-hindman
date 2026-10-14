import Hindman168.UnitTorusOptionSlabDiscrepancy
import Hindman168.UnitTorusLinearObservableInverse
import Hindman168.ScalarFractionalBracket

/-! GENUINE zero-linear-slope bracket inverse when the selected coordinate
is maximal. It PROVES a nonzero integer vector or true small real coefficients,
with ALL fixed budgets before unbounded beta/gamma/zeta and original N. -/
namespace Hindman168
open Set
open scoped BigOperators Classical

theorem unit_torus_option_zero_slope_bracket_inverse (ι : Type*) [Fintype ι]
    (Z δ B : ℝ) (hZ : 0 ≤ Z) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A : ℕ, 0 < A ∧ ∀ (β : ℝ) (ζ γ : Option ι → ℝ),
      (∀ i, |ζ i| ≤ Z) → (∀ i, |ζ i| ≤ |ζ none|) →
        ∀ N : ℕ, 0 < N →
          δ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ =>
            (N : ℝ)*‖(scalarFractionalBracket β 0 ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)).card →
            (∀ i, (N : ℝ)*|ζ i| ≤ (A : ℝ)) ∨
              ∃ k : Option ι → ℤ, k ≠ 0 ∧ (∑ i, (k i).natAbs) ≤ A ∧
                (N : ℝ)*‖((∑ i, (k i : ℝ)*γ i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨c,η,hc,hη,hdetect⟩ := unit_torus_option_slab_discrepancy ι Z δ hZ hδ hδ1
  obtain ⟨K,hK,hinv⟩ := unit_torus_linear_observable_inverse (Option ι) η hη
  let A := K+⌈B/c⌉₊+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hKA : K ≤ A := by dsimp only [A]; omega
  have hBA : B/c ≤ (A : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈B/c⌉₊ ≤ A by dsimp only [A]; omega))
  refine ⟨A,hA,?_⟩
  intro β ζ γ hζ hmax N hN hdense
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hsmall : (N : ℝ)*|ζ none| ≤ B/c
  · exact Or.inl (fun i => ((mul_le_mul_of_nonneg_left (hmax i) hn.le).trans hsmall).trans hBA)
  · have hne : ζ none ≠ 0 := by
      intro hz
      apply hsmall
      rw [hz,abs_zero,mul_zero]
      exact div_nonneg hB hc.le
    have htol : B/(N : ℝ) ≤ c*|ζ none| := by
      have hs : B/c < (N : ℝ)*|ζ none| := lt_of_not_ge hsmall
      have hh := (div_lt_iff₀ hc).mp hs
      exact (div_le_iff₀ hn).mpr (by nlinarith)
    have hset : ((Finset.range N).filter (fun h : ℕ =>
        (N : ℝ)*‖(scalarFractionalBracket β 0 ζ γ (h : ℝ) : UnitAddCircle)‖ ≤ B)) =
        (Finset.range N).filter (fun h : ℕ =>
          (fun i => (((h : ℝ)*γ i : ℝ) : UnitAddCircle)) ∈ unitTorusFractionalSlab β ζ (B/(N : ℝ))) := by
      apply Finset.filter_congr
      intro h _
      simp only [unitTorusFractionalSlab,unitTorusFractionalExpression,mem_setOf_eq,
        unit_circle_fractional_representative_real,scalarFractionalBracket,zero_mul,add_zero]
      exact (le_div_iff₀' hn).symm
    rw [hset] at hdense
    obtain ⟨F,hF,hbad⟩ := hdetect β ζ (B/(N : ℝ)) hζ hmax hne htol (Finset.range N)
      (Finset.nonempty_range_iff.mpr hN.ne') (fun h i => (((h : ℝ)*γ i : ℝ) : UnitAddCircle))
      (by simpa only [Finset.card_range] using hdense)
    obtain ⟨k,hk,hsize,hbound⟩ := hinv γ N hN F hF hbad
    exact Or.inr ⟨k,hk,hsize.trans hKA,hbound.trans (by exact_mod_cast hKA)⟩

end Hindman168
