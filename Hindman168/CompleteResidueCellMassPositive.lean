import Hindman168.CompleteResidueCellMassError

namespace Hindman168
open scoped BigOperators

theorem completeResidueCell_integerMass_pos (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) :
    0 < ∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y := by
  have he := completeResidueCell_integerMass_sum X W k M q hM hWM r hlo hhi (fun _ => 1)
  simp only [mul_one, if_pos hr] at he
  rw [he]
  apply div_pos _ hZ
  apply Finset.sum_pos
  · intro t _
    apply one_div_pos.mpr
    have hb : (k : ℝ) * (M * q : ℕ) ≤ (completeResidueCellPoint k M q r t : ℝ) := by
      exact_mod_cast (completeResidueCellPoint_bounds k M q hM r t).1
    exact hA.trans_le hb
  · exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩

theorem completeResidueCell_integerMass_unnormalized_error (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) (F : ℤ → ℝ) (hF : ∀ y, |F y| ≤ 1) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) -
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) *
      finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t))| ≤
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) *
      ((M * q : ℕ) / ((k : ℝ) * (M * q : ℕ))) := by
  have hp := completeResidueCell_integerMass_pos X W k M q hM hq hWM r hr hZ hlo hhi hA
  have he := completeResidueCell_integerMass_error X W k M q hM hq hWM r hr hZ hlo hhi hA F hF
  have hm := mul_le_mul_of_nonneg_left he hp.le
  conv_lhs at hm => lhs; rw [← abs_of_pos hp]
  rw [← abs_mul] at hm
  simp only [mul_sub, mul_div_cancel₀ _ (ne_of_gt hp)] at hm
  exact hm

end Hindman168

