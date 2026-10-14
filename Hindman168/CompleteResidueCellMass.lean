import Hindman168.CompleteResidueCellHarmonic
import Hindman168.HarmonicMass

namespace Hindman168
open scoped BigOperators

theorem residue_coprime_iff (W M r n : ℕ) (hWM : W ∣ M) (hn : n % M = r) :
    n.Coprime W ↔ r.Coprime W := by
  have he : n % W = r % W := by rw [← Nat.mod_mod_of_dvd n hWM, hn]
  change n.gcd W = 1 ↔ r.gcd W = 1
  rw [Nat.gcd_comm n W, Nat.gcd_rec W n, Nat.gcd_comm r W, Nat.gcd_rec W r, he]

theorem integerMass_on_residue_cell (X W M r : ℕ) (hWM : W ∣ M)
    (y : ℤ) (hlo : (X : ℤ) ≤ y) (hhi : y < (X ^ 2 : ℕ)) (hres : y % M = r) :
    integerMass X W y =
      if r.Coprime W then (1 / (y : ℝ)) / harmonicNormalizer X W else 0 := by
  have hy : 0 ≤ y := (Int.natCast_nonneg X).trans hlo
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  have hn : n % M = r := by exact_mod_cast hres
  have hlow : X ≤ n := by exact_mod_cast hlo
  have hhigh : n < X ^ 2 := by exact_mod_cast hhi
  rw [integerMass_apply_nat]
  simp only [harmonicWeight, harmonicWindow, Finset.mem_filter, Finset.mem_Ico,
    hlow, hhigh, true_and, residue_coprime_iff W M r n hWM hn, Int.cast_natCast, one_div]

theorem completeResidueCell_integerMass_sum (X W : ℕ) (k : ℤ) (M q : ℕ)
    (hM : 0 < M) (hWM : W ∣ M) (r : Fin M)
    (hlo : (X : ℤ) ≤ k * (M * q : ℕ))
    (hhi : k * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ)) (F : ℤ → ℝ) :
    (∑ y ∈ intervalResidueSet (k * (M * q : ℕ)) (M * q) M r.val,
      integerMass X W y * F y) =
    if r.val.Coprime W then
      (∑ t : Fin q, (1 / (completeResidueCellPoint k M q r t : ℝ)) *
        F (completeResidueCellPoint k M q r t)) / harmonicNormalizer X W else 0 := by
  rw [completeResidueCell_sum k M q hM]
  have hw (t : Fin q) := integerMass_on_residue_cell X W M r.val hWM
    (completeResidueCellPoint k M q r t)
    (hlo.trans (completeResidueCellPoint_bounds k M q hM r t).1)
    ((completeResidueCellPoint_bounds k M q hM r t).2.trans_le hhi)
    (completeResidueCellPoint_residue k M q r t)
  simp_rw [hw]
  split_ifs with hr
  · simp_rw [div_mul_eq_mul_div]
    exact (Finset.sum_div _ _ _).symm
  · simp

end Hindman168
