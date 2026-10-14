import Hindman168.CompleteResidueCellMassAggregate
import Hindman168.FiniteHaarIdentities
import Mathlib.Algebra.BigOperators.Field

namespace Hindman168
open scoped BigOperators Classical

theorem completeResidueCell_integerMass_bounded_error (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) (F : ℤ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ y, |F y| ≤ B) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) /
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) -
    finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t))| ≤
      B * ((M * q : ℕ) / ((k : ℝ) * (M * q : ℕ))) := by
  by_cases hB0 : B = 0
  · subst B
    have hz (y : ℤ) : F y = 0 := abs_eq_zero.mp (le_antisymm (hF y) (abs_nonneg _))
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_div, finiteHaarMean,
      sub_zero, abs_zero, zero_mul]
    exact le_rfl
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have hu (y : ℤ) : |F y / B| ≤ 1 := by
      rw [abs_div, abs_of_pos hBp, div_le_one hBp]
      exact hF y
    have he := completeResidueCell_integerMass_error X W k M q hM hq hWM r hr hZ hlo hhi hA
      (fun y => F y / B) hu
    have hs : (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
        integerMass X W y * (F y / B)) =
      (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
        integerMass X W y * F y) / B := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hm : finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t) / B) =
        finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t)) / B := by
      simp only [div_eq_mul_inv]
      exact finiteHaarMean_mul_const _ _
    rw [hs, hm] at he
    have hn (a b c : ℝ) : a / B / c - b / B = (a / c - b) / B := by ring
    rw [hn, abs_div, abs_of_pos hBp] at he
    exact ((div_le_iff₀ hBp).mp he).trans_eq (mul_comm _ _)

theorem completeResidueCell_integerMass_bounded_unnormalized_error (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M) (r : Fin M) (hr : r.val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (hA : 0 < (k : ℝ) * (M * q : ℕ)) (F : ℤ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hF : ∀ y, |F y| ≤ B) :
    |(∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) -
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) *
      finiteHaarMean (fun t : Fin q => F (completeResidueCellPoint k M q r t))| ≤
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val, integerMass X W y) *
      (B * ((M * q : ℕ) / ((k : ℝ) * (M * q : ℕ)))) := by
  have hp := completeResidueCell_integerMass_pos X W k M q hM hq hWM r hr hZ hlo hhi hA
  have he := completeResidueCell_integerMass_bounded_error X W k M q hM hq hWM r hr
    hZ hlo hhi hA F B hB hF
  have hm := mul_le_mul_of_nonneg_left he hp.le
  conv_lhs at hm => lhs; rw [← abs_of_pos hp]
  rw [← abs_mul] at hm
  simpa only [mul_sub, mul_div_cancel₀ _ (ne_of_gt hp)] using hm

theorem completeResidueCells_integerMass_bounded_aggregate_error {ι : Type*} [Fintype ι]
    (X W M q : ℕ) (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M)
    (k : ι → ℤ) (r : ι → Fin M) (hr : ∀ c, (r c).val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : ∀ c, (X : ℤ) ≤ k c * (M * q : ℕ))
    (hhi : ∀ c, k c * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (F : ι → ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ c y, |F c y| ≤ B) :
    let cell := fun c => intervalResidueSet (k c * (M * q : ℕ)) (M * q) M (r c).val
    let mass := fun c => ∑ y ∈ cell c, integerMass X W y
    |(∑ c, ∑ y ∈ cell c, integerMass X W y * F c y) -
      ∑ c, mass c * finiteHaarMean (fun t : Fin q => F c (completeResidueCellPoint (k c) M q (r c) t))| ≤
      (∑ c, mass c) * (B * ((M * q : ℕ) / (X : ℝ))) := by
  intro cell mass
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have ha c : (X : ℝ) ≤ (k c : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo c
  have hp c : 0 < mass c := completeResidueCell_integerMass_pos X W (k c) M q hM hq
    hWM (r c) (hr c) hZ (hlo c) (hhi c) (hx.trans_le (ha c))
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |(∑ y ∈ cell c, integerMass X W y * F c y) -
        mass c * finiteHaarMean (fun t : Fin q => F c (completeResidueCellPoint (k c) M q (r c) t))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, mass c * (B * ((M * q : ℕ) / (X : ℝ))) := by
      apply Finset.sum_le_sum
      intro c _
      exact (completeResidueCell_integerMass_bounded_unnormalized_error X W (k c) M q hM hq hWM
        (r c) (hr c) hZ (hlo c) (hhi c) (hx.trans_le (ha c)) (F c) B hB (hF c)).trans
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (Nat.cast_nonneg (M * q)) hx (ha c)) hB) (hp c).le)
    _ = _ := (Finset.sum_mul _ _ _).symm

end Hindman168
