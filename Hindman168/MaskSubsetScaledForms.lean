import Hindman168.MaskInitialSubsetForms
import Hindman168.MasterChainColumnRatios

/-! The exact normalized integer forms equal the paper's rational forms
when the original anchor coefficient divides every active coefficient.
Multiplying by the anchor recovers the actual sum of scaled coordinates. -/

namespace Hindman168
open scoped BigOperators Classical

theorem maskSubsetIntegerForm_scaled {m : ℕ} (c : Fin (m+1) → ℕ)
    (U : NonemptyColumnSubset (m+1))
    (hd : ∀ k ∈ U.val, c (U.val.max' U.property) ∣ c k) (z : Fin (m+1) → ℤ) :
    (c (U.val.max' U.property) : ℤ) * maskSubsetIntegerForm c U z =
      ∑ k ∈ U.val, (c k : ℤ) * z k := by
  unfold maskSubsetIntegerForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (c (U.val.max' U.property) : ℤ) * (c k / c (U.val.max' U.property) : ℕ) = c k := by
    exact_mod_cast ((Nat.mul_comm _ _).trans (Nat.div_mul_cancel (hd k hk)))
  rw [← mul_assoc, he]

theorem maskSubsetIntegerForm_rational {m : ℕ} (c : Fin (m+1) → ℕ)
    (U : NonemptyColumnSubset (m+1)) (hc : 0 < c (U.val.max' U.property))
    (hd : ∀ k ∈ U.val, c (U.val.max' U.property) ∣ c k) (z : Fin (m+1) → ℤ) :
    (maskSubsetIntegerForm c U z : ℚ) =
      ∑ k ∈ U.val, ((c k : ℚ) / c (U.val.max' U.property)) * (z k : ℚ) := by
  unfold maskSubsetIntegerForm
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_div (hd k hk) (by exact_mod_cast hc.ne')]

theorem maskSubsetIntegerForm_positive {m : ℕ} (c : Fin (m+1) → ℕ)
    (hc : ∀ k, 0 < c k) (U : NonemptyColumnSubset (m+1))
    (z : Fin (m+1) → ℕ) (hz : 0 < z (U.val.max' U.property)) :
    0 < maskSubsetIntegerForm c U (fun k => (z k : ℤ)) := by
  have hl := Finset.single_le_sum (s := U.val)
    (f := fun k => ((c k / c (U.val.max' U.property) : ℕ) : ℤ) * z k)
    (fun k _ => by positivity) (Finset.max'_mem U.val U.property)
  rw [Nat.div_self (hc _), Nat.cast_one, one_mul] at hl
  exact (Int.natCast_pos.mpr hz).trans_le hl

theorem maskSubsetIntegerForm_natural_scaled {m : ℕ} (c : Fin (m+1) → ℕ)
    (U : NonemptyColumnSubset (m+1))
    (hd : ∀ k ∈ U.val, c (U.val.max' U.property) ∣ c k) (z : Fin (m+1) → ℕ) :
    c (U.val.max' U.property) * (maskSubsetIntegerForm c U (fun k => (z k : ℤ))).toNat =
      ∑ k ∈ U.val, c k * z k := by
  have hn : 0 ≤ maskSubsetIntegerForm c U (fun k => (z k : ℤ)) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  have he := maskSubsetIntegerForm_scaled c U hd (fun k => (z k : ℤ))
  rw [Int.eq_natCast_toNat.mpr hn] at he
  exact_mod_cast he

theorem MasterParameterConditions.subset_scaled_forms {n N m : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (a : Fin (m+1) → ℚ)
    (ha : ∀ k, a k ∈ A) (C : ℕ → Chain (m+1))
    (hC : ∀ w k, (C w).block k ⊆ Finset.range N) :
    ∀ᶠ w in Filter.atTop,
      let c := masterColumnCoefficient N a (fun w => (C w).block) w
      (∀ k, 0 < c k) ∧ ∀ U : NonemptyColumnSubset (m+1),
        (∀ k ∈ U.val, c (U.val.max' U.property) ∣ c k) ∧
        (∀ z : Fin (m+1) → ℤ,
          (c (U.val.max' U.property) : ℤ) * maskSubsetIntegerForm c U z =
            ∑ k ∈ U.val, (c k : ℤ) * z k) ∧
        (∀ z : Fin (m+1) → ℤ,
          (maskSubsetIntegerForm c U z : ℚ) =
            ∑ k ∈ U.val,
              (((masterScale (primorial w) w N ((C w).block k) : ℚ) * a k) /
                ((masterScale (primorial w) w N ((C w).block (U.val.max' U.property)) : ℚ) *
                  a (U.val.max' U.property))) * (z k : ℚ)) := by
  have hc := hF.column_coefficients a ha (fun w => (C w).block) hC
    (fun w k => (C w).block_nonempty k)
  have hr := hF.chain_column_ratios a ha C hC
  filter_upwards [hc, hr] with w hw hratio
  refine ⟨fun k => (hw k).1, ?_⟩
  intro U
  have hd (k : Fin (m+1)) (hk : k ∈ U.val) :
      masterColumnCoefficient N a (fun w => (C w).block) w (U.val.max' U.property) ∣
        masterColumnCoefficient N a (fun w => (C w).block) w k := by
    have hl := U.val.le_max' k hk
    rcases eq_or_lt_of_le hl with he | he
    · rw [he]
    · exact (hratio k _ he).1
  refine ⟨hd, maskSubsetIntegerForm_scaled _ U hd, ?_⟩
  intro z
  rw [maskSubsetIntegerForm_rational _ U (hw _).1 hd]
  simp only [(hw _).2.1]

end Hindman168
