import Hindman168.AlignmentIntegerNumerators
import Hindman168.MasterSamplingBudgets
import Hindman168.AlignmentIntegerResidues

/-! Polynomial bounds for the actual numerator and displacement, uniform
over earlier raw values in their original cutoffs. -/

namespace Hindman168

open scoped BigOperators Classical

theorem alignment_earlier_block_product_bound
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (w : ℕ) (i : Fin n) (t : Fin n → ℕ)
    (ht : ∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2)
    (S : Finset (Fin n)) (hS : ∀ j ∈ S, j < i) :
    alignmentNaturalBlockProduct t S ≤ F.auxiliary w i.val := by
  have hs : alignmentNaturalBlock S ⊆ Finset.range i.val := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hS k hk)
  have he : (∏ j ∈ alignmentNaturalBlock S, F.cutoff w j ^ 2) =
      ∏ j ∈ S, F.cutoff w j.val ^ 2 := by
    rw [alignmentNaturalBlock, Finset.prod_image]
    exact fun _ _ _ _ hh => Fin.ext hh
  have hb := hF.earlier_tail_product_bound w i.val (alignmentNaturalBlock S) hs
  rw [he] at hb
  exact (Finset.prod_le_prod' (fun j hj => ht j (hS j hj))).trans hb

theorem alignmentIntegerNumerator_polynomial_bound
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) {i : Fin n} (t : Fin n → ℕ)
    (ht : ∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2) (e : AlignmentAddingPair n i) :
    alignmentIntegerNumerator q₀ w e t ≤ F.auxiliary w i.val ^ 2 := by
  have hs : alignmentIntegerScale w (alignmentPairSourceBlock e) ≤ (F.modulus w : ℕ) :=
    hF.subset_scale_le w _ (alignmentNaturalBlock_subset _)
  have hp := alignment_earlier_block_product_bound hF w i t ht _ (alignmentPair_source_before e)
  unfold alignmentIntegerNumerator
  have hd := (Nat.div_le_self (alignmentIntegerScale w (alignmentPairSourceBlock e))
    (q₀ * alignmentIntegerScale w (alignmentPairTargetBlock e))).trans hs
  have hm := Nat.mul_le_mul hd hp
  exact hm.trans (by simpa only [pow_two] using
    Nat.mul_le_mul_right (F.auxiliary w i.val) (F.modulus_le_auxiliary w i.val))

theorem alignmentProgressionShift_polynomial_bound
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (q₀ w : ℕ) {i : Fin n} (t : Fin n → ℕ)
    (ht : ∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2) (e : AlignmentAddingPair n i)
    (ρ : ℕ) (hρ : ρ ≤ (F.modulus w : ℕ) ^ 2) (Δ : ℤ)
    (hexact : (F.modulus w : ℤ) * Δ = (alignmentIntegerNumerator q₀ w e t : ℤ) -
      (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ) :
    |(F.modulus w : ℤ) * Δ| ≤ 2 * (F.auxiliary w i.val : ℤ) ^ 3 := by
  have hq : (alignmentIntegerNumerator q₀ w e t : ℤ) ≤ (F.auxiliary w i.val : ℤ) ^ 2 := by
    exact_mod_cast alignmentIntegerNumerator_polynomial_bound hF q₀ w t ht e
  have htt : (alignmentNaturalBlockProduct t e.targetTail : ℤ) ≤ F.auxiliary w i.val := by
    exact_mod_cast alignment_earlier_block_product_bound hF w i t ht _ (alignmentPair_target_before e)
  have hr : (ρ : ℤ) ≤ (F.auxiliary w i.val : ℤ) ^ 2 := by
    exact_mod_cast hρ.trans (Nat.pow_le_pow_left (F.modulus_le_auxiliary w i.val) 2)
  have htr := mul_le_mul htt hr (Int.natCast_nonneg ρ) (Int.natCast_nonneg _)
  have ha : (2 : ℤ) ≤ F.auxiliary w i.val := by exact_mod_cast F.auxiliary_ge_two w i.val
  rw [hexact]
  have hab : |(alignmentIntegerNumerator q₀ w e t : ℤ) -
      (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ| ≤
      |(alignmentIntegerNumerator q₀ w e t : ℤ)| + |(alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (alignmentIntegerNumerator q₀ w e t : ℤ) (-((alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ))
  have hq0 : (0 : ℤ) ≤ alignmentIntegerNumerator q₀ w e t := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  rw [abs_of_nonneg hq0, abs_of_nonneg hp0] at hab
  nlinarith [sq_nonneg (F.auxiliary w i.val : ℤ)]

end Hindman168
