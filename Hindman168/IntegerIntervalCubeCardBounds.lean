import Hindman168.IntegerIntervalCubeDomain
import Mathlib.Data.Fintype.BigOperators

namespace Hindman168
open scoped BigOperators Classical symmDiff

/-- Fixing one vertex to an integer strip and all its neighbors to
[0,L) bounds the number of actual cube parameters in that strip. -/
theorem integerIntervalCubeDomain_vertex_strip_card_le (d L : ℕ)
    (ω : Finset (Fin d)) (a b : ℤ) :
    ((integerIntervalCubeDomain d L).filter (fun p =>
      a ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < b)).card ≤
      (b - a).toNat * L ^ d := by
  let B := (Finset.Ico a b).product
    (Fintype.piFinset (fun _ : Fin d => Finset.Ico 0 (L : ℤ)))
  have hb : Set.MapsTo (integerCubeCornerCoordinates ω)
      ((integerIntervalCubeDomain d L).filter (fun p =>
        a ≤ integerCubeVertex p ω ∧ integerCubeVertex p ω < b)) B := by
    intro p hp
    obtain ⟨hp, hs⟩ := Finset.mem_filter.mp hp
    have hall := (mem_integerIntervalCubeDomain p).mp hp
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Ico.mpr hs,
      Fintype.mem_piFinset.mpr (fun j => Finset.mem_Ico.mpr (hall (ω ∆ {j})))⟩
  have hc := Finset.card_le_card_of_injOn (integerCubeCornerCoordinates ω) hb
    (integerCubeCornerCoordinates_injective ω).injOn
  have hB : B.card = (b - a).toNat * L ^ d := by
    dsimp only [B]
    rw [Finset.product_eq_sprod, Finset.card_product, Fintype.card_piFinset]
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  exact hc.trans_eq hB

/-- A genuine nonnegative parameter box gives a uniform lower bound
for the full signed-increment interval cube domain. -/
theorem integerIntervalCubeDomain_card_lower_box (d L H : ℕ)
    (hH : (d + 1) * H ≤ L) : H ^ (d + 1) ≤ (integerIntervalCubeDomain d L).card := by
  let B := (Finset.Ico 0 (H : ℤ)).product
    (Fintype.piFinset (fun _ : Fin d => Finset.Ico 0 (H : ℤ)))
  have hsubset : B ⊆ integerIntervalCubeDomain d L := by
    intro p hp
    obtain ⟨hr, hv⟩ := Finset.mem_product.mp hp
    have hr' := Finset.mem_Ico.mp hr
    have hv' (j : Fin d) := Finset.mem_Ico.mp (Fintype.mem_piFinset.mp hv j)
    apply (mem_integerIntervalCubeDomain p).mpr
    intro ω
    have hsum0 : 0 ≤ ∑ j ∈ ω, p.2 j := Finset.sum_nonneg (fun j _ => (hv' j).1)
    have hsum : (∑ j ∈ ω, p.2 j) ≤ (d : ℤ) * H := by
      calc
        _ ≤ ∑ _j ∈ ω, (H : ℤ) := Finset.sum_le_sum (fun j _ => (hv' j).2.le)
        _ = (ω.card : ℤ) * H := by simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by
          have hc : ω.card ≤ d := by simpa only [Fintype.card_fin] using Finset.card_le_univ ω
          exact_mod_cast hc) (Nat.cast_nonneg H)
    have hHI : ((d : ℤ) + 1) * H ≤ L := by exact_mod_cast hH
    change 0 ≤ p.1 + (∑ j ∈ ω, p.2 j) ∧ p.1 + (∑ j ∈ ω, p.2 j) < L
    constructor <;> nlinarith [hr'.1, hr'.2]
  have hc := Finset.card_le_card hsubset
  have hB : B.card = H ^ (d + 1) := by
    dsimp only [B]
    rw [Finset.product_eq_sprod, Finset.card_product, Fintype.card_piFinset]
    simp only [Int.card_Ico, sub_zero, Int.toNat_natCast, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, pow_succ, Nat.mul_comm]
  exact hB ▸ hc

end Hindman168
