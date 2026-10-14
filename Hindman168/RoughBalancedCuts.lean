import Hindman168.RoughBoxPieceWeights

namespace Hindman168

def roughBalancedOffset (L N i : ℕ) : ℕ :=
  i * (L / N) + min i (L % N)

def roughBalancedCut (A B : ℤ) (N i : ℕ) : ℤ :=
  A + (roughBalancedOffset (B - A).toNat N i : ℤ)

theorem rough_balanced_offset_zero (L N : ℕ) : roughBalancedOffset L N 0 = 0 := by
  simp [roughBalancedOffset]

theorem rough_balanced_offset_last (L N : ℕ) (hN : 0 < N) :
    roughBalancedOffset L N N = L := by
  simp only [roughBalancedOffset, min_eq_right (Nat.mod_lt L hN).le]
  exact Nat.div_add_mod L N

theorem rough_balanced_offset_mono (L N : ℕ) : Monotone (roughBalancedOffset L N) := by
  intro i j hij
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hij) (min_le_min_right _ hij)

theorem rough_balanced_offset_step (L N i : ℕ) :
    L / N ≤ roughBalancedOffset L N (i + 1) - roughBalancedOffset L N i ∧
    roughBalancedOffset L N (i + 1) - roughBalancedOffset L N i ≤ L / N + 1 := by
  simp only [roughBalancedOffset, Nat.add_mul, one_mul]
  have hmin : min i (L % N) ≤ min (i + 1) (L % N) := min_le_min_right _ (by omega)
  have hmax : min (i + 1) (L % N) ≤ min i (L % N) + 1 := by omega
  have hq := Nat.zero_le (L / N)
  omega

theorem rough_balanced_cut_endpoints (A B : ℤ) (N : ℕ) (hAB : A ≤ B) (hN : 0 < N) :
    roughBalancedCut A B N 0 = A ∧ roughBalancedCut A B N N = B := by
  simp only [roughBalancedCut, rough_balanced_offset_zero, Nat.cast_zero, add_zero,
    rough_balanced_offset_last _ _ hN]
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hAB)]
  exact ⟨True.intro, by omega⟩

theorem rough_balanced_cut_mono (A B : ℤ) (N : ℕ) :
    Monotone (roughBalancedCut A B N) := by
  intro i j hij
  simp only [roughBalancedCut]
  have hh : (roughBalancedOffset (B-A).toNat N i : ℤ) ≤ roughBalancedOffset (B-A).toNat N j := by
    exact_mod_cast rough_balanced_offset_mono (B-A).toNat N hij
  exact add_le_add_right hh A

theorem rough_balanced_cut_contained (A B : ℤ) (N i : ℕ)
    (hAB : A ≤ B) (hN : 0 < N) (hi : i ≤ N) :
    A ≤ roughBalancedCut A B N i ∧ roughBalancedCut A B N i ≤ B := by
  have he := rough_balanced_cut_endpoints A B N hAB hN
  exact ⟨by simpa only [he.1] using rough_balanced_cut_mono A B N (Nat.zero_le i),
    by simpa only [he.2] using rough_balanced_cut_mono A B N hi⟩

theorem rough_balanced_cut_step (A B : ℤ) (N i : ℕ) :
    (((B - A).toNat / N : ℕ) : ℤ) ≤ roughBalancedCut A B N (i+1) - roughBalancedCut A B N i ∧
    roughBalancedCut A B N (i+1) - roughBalancedCut A B N i ≤ ((B-A).toNat / N : ℕ) + 1 := by
  have hm := rough_balanced_offset_mono (B-A).toNat N (show i ≤ i+1 by omega)
  have hs := rough_balanced_offset_step (B-A).toNat N i
  rw [roughBalancedCut, roughBalancedCut, add_sub_add_left_eq_sub,
    ← Nat.cast_sub hm]
  constructor
  · exact_mod_cast hs.1
  · exact_mod_cast hs.2

theorem rough_balanced_cut_real_bounds (A B : ℤ) (N i : ℕ)
    (hN : 0 < N) (hlen : 2 * (N : ℤ) ≤ B - A) :
    ((B : ℝ) - A) / (2 * N) ≤
      (roughBalancedCut A B N (i+1) : ℝ) - roughBalancedCut A B N i ∧
    (roughBalancedCut A B N (i+1) : ℝ) - roughBalancedCut A B N i ≤
      2 * ((B : ℝ) - A) / N := by
  have hAB : A ≤ B := by omega
  have hcast : (((B-A).toNat : ℕ) : ℤ) = B-A := Int.toNat_of_nonneg (sub_nonneg.mpr hAB)
  have hL : 2 * N ≤ (B-A).toNat := by
    have hh : (2 * N : ℤ) ≤ ((B-A).toNat : ℤ) := by rw [hcast]; exact hlen
    exact_mod_cast hh
  have hq : 2 ≤ (B-A).toNat / N := (Nat.le_div_iff_mul_le hN).mpr (by omega)
  have hd := Nat.div_add_mod (B-A).toNat N
  have hr := Nat.mod_lt (B-A).toNat hN
  have hdR : (N : ℝ) * ((B-A).toNat / N : ℕ) + ((B-A).toNat % N : ℕ) = (B : ℝ) - A := by
    have hh : (((B-A).toNat : ℕ) : ℝ) = (B : ℝ) - A := by exact_mod_cast hcast
    rw [← hh]
    exact_mod_cast hd
  have hrR : (((B-A).toNat % N : ℕ) : ℝ) < N := by exact_mod_cast hr
  have hqR : (2 : ℝ) ≤ ((B-A).toNat / N : ℕ) := by exact_mod_cast hq
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := rough_balanced_cut_step A B N i
  have hsR : (((B-A).toNat / N : ℕ) : ℝ) ≤
      (roughBalancedCut A B N (i+1) : ℝ) - roughBalancedCut A B N i ∧
      (roughBalancedCut A B N (i+1) : ℝ) - roughBalancedCut A B N i ≤
        (((B-A).toNat / N : ℕ) : ℝ) + 1 := by
    constructor
    · have hh := (Int.cast_le (R := ℝ)).mpr hs.1
      simpa only [Int.cast_natCast, Int.cast_sub] using hh
    · have hh := (Int.cast_le (R := ℝ)).mpr hs.2
      simpa only [Int.cast_natCast, Int.cast_sub, Int.cast_add, Int.cast_one] using hh
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*N)).mpr
    nlinarith
  · apply (le_div_iff₀ hNr).mpr
    have hr0 : (0 : ℝ) ≤ ((B-A).toNat % N : ℕ) := by positivity
    nlinarith

end Hindman168
