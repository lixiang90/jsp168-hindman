import Hindman168.Chain
import Hindman168.Scales

/-!
# Reversed master weights on the actual index set

For zero-based indices `j < N`, the paper's one-based `2^(N-j)` is
`2^(N-1-j)`. Reflection is injective on `range N`. This file connects the
binary-weight arithmetic to the ordered adding-block relation, and supplies
a common power-of-`W` modulus. It does not yet construct the asymptotic
harmonic/prime parameters of the full master-scales lemma.
-/

namespace Hindman168

open scoped BigOperators

def reverseSubset (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (fun j => N - 1 - j)

def reversedWeight (N : ℕ) (S : Finset ℕ) : ℕ := binaryWeight (reverseSubset N S)

def masterScale (W w N : ℕ) (S : Finset ℕ) : ℕ := W ^ (w * reversedWeight N S)

def commonModulus (W w N : ℕ) : ℕ := W ^ (w * binaryWeight (Finset.range N))

theorem reverseSubset_subset {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    reverseSubset N S ⊆ Finset.range N := by
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  have hkN := Finset.mem_range.mp (hS hk)
  apply Finset.mem_range.mpr
  omega

/-- The subset master scale is exactly the product of the individual ones. -/
theorem masterScale_product {N : ℕ} {S : Finset ℕ} (W w : ℕ)
    (hS : S ⊆ Finset.range N) :
    (∏ j ∈ S, W ^ (w * 2 ^ (N - 1 - j))) = masterScale W w N S := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => N - 1 - j) (↑S : Set ℕ) := by
    intro a ha b hb hab
    change N - 1 - a = N - 1 - b at hab
    have haN := Finset.mem_range.mp (hS ha)
    have hbN := Finset.mem_range.mp (hS hb)
    omega
  have h := product_scale (reverseSubset N S) W w
  rw [reverseSubset, Finset.prod_image hinj] at h
  exact h

/-- Any index of `A` that precedes every index of `B` supplies a dominating
binary weight, hence an entire `W^w` factor in the scale ratio. -/
theorem masterScale_divisibility {N p : ℕ} {A B : Finset ℕ} (W w : ℕ)
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N) (hp : p ∈ A)
    (hbefore : ∀ b ∈ B, p < b) :
    masterScale W w N B * W ^ w ∣ masterScale W w N A := by
  have hpN := Finset.mem_range.mp (hA hp)
  have hk : N - 1 - p ∈ reverseSubset N A := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hb : reverseSubset N B ⊆ Finset.range (N - 1 - p) := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    have hjN := Finset.mem_range.mp (hB hj)
    have hpj := hbefore j hj
    apply Finset.mem_range.mpr
    omega
  exact scale_divisibility W w hk hb

/-- In particular, the exact adding-block relation in the paper implies the
required integer-multiple ratio, rather than merely a real inequality. -/
theorem adding_block_scale_divisibility {N i j : ℕ} {P T : Finset ℕ} (W w : ℕ)
    (hadd : Chain.AddsTo P j T i) (hT : T.Nonempty)
    (hA : insert j P ⊆ Finset.range N) (hB : insert i T ⊆ Finset.range N) :
    masterScale W w N (insert i T) * W ^ w ∣ masterScale W w N (insert j P) := by
  obtain ⟨p, hp⟩ := hadd.1
  apply masterScale_divisibility W w hA hB (Finset.mem_insert_of_mem hp)
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · obtain ⟨t, ht⟩ := hT
    exact (hadd.2.1 p hp t ht).trans ((hadd.2.2.1 t ht).trans hadd.2.2.2)
  · exact hadd.2.1 p hp b hb

theorem chain_scale_divisibility {m N : ℕ} (C : Chain m) (W w : ℕ)
    (hC : ∀ i, C.block i ⊆ Finset.range N) (i j : Fin m) (hij : i < j) :
    masterScale W w N (C.block j) * W ^ w ∣ masterScale W w N (C.block i) :=
  adding_block_scale_divisibility W w (C.earlier_adds i j hij)
    (C.tail_nonempty j) (hC i) (hC j)

/-- Every bounded subset scale divides the same explicit power of `W`. -/
theorem masterScale_dvd_commonModulus {N : ℕ} {S : Finset ℕ} (W w : ℕ)
    (hS : S ⊆ Finset.range N) : masterScale W w N S ∣ commonModulus W w N := by
  have hweight : reversedWeight N S ≤ binaryWeight (Finset.range N) :=
    Finset.sum_le_sum_of_subset_of_nonneg (reverseSubset_subset hS)
      (fun j _ _ => Nat.zero_le (2 ^ j))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.mul_le_mul_left w hweight)
  refine ⟨W ^ d, ?_⟩
  change W ^ (w * binaryWeight (Finset.range N)) = W ^ (w * reversedWeight N S) * W ^ d
  rw [hd, pow_add]

theorem masterScale_le_commonModulus {N : ℕ} {S : Finset ℕ} {W : ℕ} (w : ℕ)
    (hW : 0 < W) (hS : S ⊆ Finset.range N) :
    masterScale W w N S ≤ commonModulus W w N :=
  Nat.le_of_dvd (Nat.pow_pos hW) (masterScale_dvd_commonModulus W w hS)

/-- Every nonempty subset scale, including every singleton, contains `W^w`. -/
theorem power_dvd_masterScale {N : ℕ} {S : Finset ℕ} (W w : ℕ) (hS : S.Nonempty) :
    W ^ w ∣ masterScale W w N S := by
  obtain ⟨j, hj⟩ := hS
  have hsingle : (2 : ℕ) ^ (N - 1 - j) ≤ reversedWeight N S :=
    Finset.single_le_sum (fun k _ => Nat.zero_le ((2 : ℕ) ^ k))
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hpos : 0 < (2 : ℕ) ^ (N - 1 - j) := Nat.pow_pos (by decide)
  have hweight : 1 ≤ reversedWeight N S := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by
    simpa using Nat.mul_le_mul_left w hweight)
  refine ⟨W ^ d, ?_⟩
  change W ^ (w * reversedWeight N S) = W ^ w * W ^ d
  rw [hd, pow_add]

/-- For a nonempty ambient index interval, the common modulus contains `W^w`. -/
theorem power_dvd_commonModulus {N : ℕ} (W w : ℕ) (hN : 0 < N) :
    W ^ w ∣ commonModulus W w N := by
  have hweight : 1 ≤ binaryWeight (Finset.range N) := by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le ((2 : ℕ) ^ j))
      (Finset.mem_range.mpr hN)
    simpa [binaryWeight] using h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (by
    simpa using Nat.mul_le_mul_left w hweight)
  refine ⟨W ^ d, ?_⟩
  change W ^ (w * binaryWeight (Finset.range N)) = W ^ w * W ^ d
  rw [hd, pow_add]

end Hindman168
