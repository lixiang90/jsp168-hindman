import Hindman168.Basic
import Hindman168.FiniteMass
import Mathlib.Tactic

/-!
# Extracting actual sums and products from the final weighted count

The finite argument in Section 2.5 of the September 23 OpenAI paper uses
only nonvanishing of its factors. Auxiliary divisor weights cannot create
false positives. This module isolates that argument from the analytic
proof of positivity. The normalized forms are supplied with their exact
integer scaling identity, as established by `MaskSubsetScaledForms`.
-/

namespace Hindman168
open scoped BigOperators Classical
open FiniteMass

abbrev ExtractionSubset (m : ℕ) := {S : Finset (Fin m) // S.Nonempty}

noncomputable def extractionSumFactor {m r : ℕ} (c : Fin m → ℕ)
    (χ : ℕ → Fin r) (κ : Fin r) (ν : Fin m → ℤ → ℝ)
    (S : ExtractionSubset m) (y : ℤ) : ℝ :=
  ν (S.val.max' S.property) y *
    (if 0 < y then if χ (c (S.val.max' S.property) * y.toNat) = κ then 1 else 0 else 0)

noncomputable def extractionProductFactor {m r : ℕ} (c : Fin m → ℕ)
    (χ : ℕ → Fin r) (κ : Fin r) (S : Finset (Fin m)) (y : ℤ) : ℝ :=
  if 0 < y ∧ χ ((∏ k ∈ S, c k) * y.toNat) = κ then 1 else 0

noncomputable def extractionIntegrand {m r : ℕ} (c : Fin m → ℕ)
    (χ : ℕ → Fin r) (κ : Fin r) (ν : Fin m → ℤ → ℝ)
    (row : ExtractionSubset m → (Fin m → ℤ) → ℤ) (z : Fin m → ℤ) : ℝ :=
  (∏ i, ν i (z i)) *
    ((∏ S : ExtractionSubset m, if 2 ≤ S.val.card then
      extractionSumFactor c χ κ ν S (row S z) else 1) *
      ∏ S ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
        extractionProductFactor c χ κ S (∏ k ∈ S, z k))

/-- The exact color factors in a nonzero count force a genuine natural
FS/FP tuple, regardless of the auxiliary divisor weights. -/
theorem extractionIntegrand_ne_zero {m r : ℕ} (c : Fin m → ℕ)
    (χ : ℕ → Fin r) (κ : Fin r) (ν : Fin m → ℤ → ℝ)
    (row : ExtractionSubset m → (Fin m → ℤ) → ℤ) (z : Fin m → ℤ)
    (hc : ∀ i, 0 < c i)
    (hrow : ∀ S, (c (S.val.max' S.property) : ℤ) * row S z =
      ∑ k ∈ S.val, (c k : ℤ) * z k)
    (h : extractionIntegrand c χ κ ν row z ≠ 0) :
    (∀ i, 0 < z i ∧ 0 < c i * (z i).toNat) ∧
      ∀ S : Finset (Fin m), S.Nonempty →
        χ (∑ k ∈ S, c k * (z k).toNat) = κ ∧
        χ (∏ k ∈ S, c k * (z k).toNat) = κ := by
  have hinner := (mul_ne_zero_iff.mp h).2
  have hsumprod := (mul_ne_zero_iff.mp hinner).1
  have hprodprod := (mul_ne_zero_iff.mp hinner).2
  have hproduct (S : Finset (Fin m)) (hS : S.Nonempty) :
      0 < ∏ k ∈ S, z k ∧
      χ ((∏ k ∈ S, c k) * (∏ k ∈ S, z k).toNat) = κ := by
    have hmem : S ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅ := by
      simp [Finset.nonempty_iff_ne_empty.mp hS]
    have hf := (Finset.prod_ne_zero_iff.mp hprodprod) S hmem
    unfold extractionProductFactor at hf
    split_ifs at hf with hh
    · exact hh
    · exact (hf rfl).elim
  have hz (i : Fin m) : 0 < z i := by
    simpa using (hproduct {i} (by simp)).1
  have hcast (i : Fin m) : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hz i).le
  have hproducts (S : Finset (Fin m)) (hS : S.Nonempty) :
      χ (∏ k ∈ S, c k * (z k).toNat) = κ := by
    have he : (∏ k ∈ S, z k).toNat = ∏ k ∈ S, (z k).toNat := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.toNat_of_nonneg (hproduct S hS).1.le]
      push_cast
      simp only [hcast]
    simpa [he, Finset.prod_mul_distrib] using (hproduct S hS).2
  have hzNat (i : Fin m) : 0 < (z i).toNat := by
    exact_mod_cast (show (0 : ℤ) < ((z i).toNat : ℤ) by rw [hcast]; exact hz i)
  refine ⟨fun i => ⟨hz i, Nat.mul_pos (hc i) (hzNat i)⟩, ?_⟩
  intro S hS
  refine ⟨?_, hproducts S hS⟩
  by_cases hcard : 2 ≤ S.card
  · let U : ExtractionSubset m := ⟨S, hS⟩
    have hf := (Finset.prod_ne_zero_iff.mp hsumprod) U (Finset.mem_univ U)
    simp only [U, hcard, ↓reduceIte] at hf
    have hcolor : 0 < row U z ∧ χ (c (S.max' hS) * (row U z).toNat) = κ := by
      unfold extractionSumFactor at hf
      split_ifs at hf with hy hχ
      · exact ⟨hy, hχ⟩
      · simp at hf
      · simp at hf
    have he : c (S.max' hS) * (row U z).toNat = ∑ k ∈ S, c k * (z k).toNat := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg hcolor.1.le]
      simp only [hcast]
      exact hrow U
    exact he ▸ hcolor.2
  · have hone : S.card = 1 := by have := hS.card_pos; omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    simpa using hproducts {i} (by simp)

/-- A positive finite weighted count contains a support point with all
required colors. No positivity assumption on the extra weights is needed. -/
theorem positive_color_count_extract {m r : ℕ} (c : Fin m → ℕ)
    (χ : ℕ → Fin r) (κ : Fin r) (ν : Fin m → ℤ → ℝ)
    (row : ExtractionSubset m → (Fin m → ℤ) → ℤ)
    (μ : Mass (Fin m → ℤ)) (hc : ∀ i, 0 < c i)
    (hrow : ∀ z ∈ μ.support, ∀ S, (c (S.val.max' S.property) : ℤ) * row S z =
      ∑ k ∈ S.val, (c k : ℤ) * z k)
    (hcount : 0 < expectation μ (extractionIntegrand c χ κ ν row)) :
    ∃ z ∈ μ.support, (∀ i, 0 < z i ∧ 0 < c i * (z i).toNat) ∧
      ∀ S : Finset (Fin m), S.Nonempty →
        χ (∑ k ∈ S, c k * (z k).toNat) = κ ∧
        χ (∏ k ∈ S, c k * (z k).toNat) = κ := by
  have hex : ∃ z ∈ μ.support, extractionIntegrand c χ κ ν row z ≠ 0 := by
    by_contra hn
    push Not at hn
    have he : expectation μ (extractionIntegrand c χ κ ν row) = 0 := by
      unfold expectation Finsupp.sum
      apply Finset.sum_eq_zero
      intro z hz
      simp [hn z hz]
    linarith
  obtain ⟨z, hz, hn⟩ := hex
  exact ⟨z, hz, extractionIntegrand_ne_zero c χ κ ν row z hc (hrow z hz) hn⟩

end Hindman168
