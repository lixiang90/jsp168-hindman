import Hindman168.IntegerPeriodicCubeAverage

namespace Hindman168
open scoped BigOperators Classical

/-- Every canonical residue-parameter shift moves each integer cube
vertex by a nonnegative amount at most (d+1)(q-1), uniformly in that vertex. -/
theorem integerCubeResidueShift_vertex_bounds (q d : ℕ) [NeZero q]
    (r : ZMod q × (Fin d → ZMod q)) (ω : Finset (Fin d)) :
    0 ≤ integerCubeVertex (integerCubeResidueShift q d r) ω ∧
      integerCubeVertex (integerCubeResidueShift q d r) ω ≤ ((d + 1) * (q - 1) : ℕ) := by
  have hroot : (r.1.val : ℤ) ≤ (q - 1 : ℕ) := by
    exact_mod_cast Nat.le_pred_of_lt (ZMod.val_lt r.1)
  have hdir (j : Fin d) : ((r.2 j).val : ℤ) ≤ (q - 1 : ℕ) := by
    exact_mod_cast Nat.le_pred_of_lt (ZMod.val_lt (r.2 j))
  have hsum0 : (0 : ℤ) ≤ ∑ j ∈ ω, ((r.2 j).val : ℤ) :=
    Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)
  have hsum : (∑ j ∈ ω, ((r.2 j).val : ℤ)) ≤ (d : ℤ) * (q - 1 : ℕ) := by
    calc
      _ ≤ ∑ _j ∈ ω, ((q - 1 : ℕ) : ℤ) := Finset.sum_le_sum (fun j _ => hdir j)
      _ = (ω.card : ℤ) * (q - 1 : ℕ) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        have hc : ω.card ≤ d := by simpa only [Fintype.card_fin] using Finset.card_le_univ ω
        exact_mod_cast hc) (Nat.cast_nonneg _)
  change 0 ≤ (r.1.val : ℤ) + (∑ j ∈ ω, ((r.2 j).val : ℤ)) ∧ _
  constructor
  · exact add_nonneg (Nat.cast_nonneg _) hsum0
  · change (r.1.val : ℤ) + (∑ j ∈ ω, ((r.2 j).val : ℤ)) ≤ ((d + 1) * (q - 1) : ℕ)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    nlinarith

end Hindman168
