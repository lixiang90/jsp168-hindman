import Hindman168.CompleteResidueCellMassPositive

namespace Hindman168
open scoped BigOperators

theorem completeResidueCells_integerMass_aggregate_error {ι : Type*} [Fintype ι]
    (X W M q : ℕ) (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M)
    (k : ι → ℤ) (r : ι → Fin M) (hr : ∀ c, (r c).val.Coprime W)
    (hZ : 0 < harmonicNormalizer X W)
    (hlo : ∀ c, (X : ℤ) ≤ k c * (M * q : ℕ))
    (hhi : ∀ c, k c * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (F : ι → ℤ → ℝ) (hF : ∀ c y, |F c y| ≤ 1) :
    let cell := fun c => intervalResidueSet (k c * (M * q : ℕ)) (M * q) M (r c).val
    let mass := fun c => ∑ y ∈ cell c, integerMass X W y
    |(∑ c, ∑ y ∈ cell c, integerMass X W y * F c y) -
      ∑ c, mass c * finiteHaarMean (fun t : Fin q => F c (completeResidueCellPoint (k c) M q (r c) t))| ≤
      (∑ c, mass c) * ((M * q : ℕ) / (X : ℝ)) := by
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
    _ ≤ ∑ c, mass c * ((M * q : ℕ) / (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro c _
      exact (completeResidueCell_integerMass_unnormalized_error X W (k c) M q hM hq hWM
        (r c) (hr c) hZ (hlo c) (hhi c) (hx.trans_le (ha c)) (F c) (hF c)).trans
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Nat.cast_nonneg (M * q)) hx (ha c)) (hp c).le)
    _ = _ := (Finset.sum_mul _ _ _).symm

end Hindman168
