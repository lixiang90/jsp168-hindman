import Hindman168.AlignmentCubeCoordinates

namespace Hindman168

theorem alignmentCubeBase_rounding_error (M t p Q ell : ℤ) (hM : 0 < M) :
    |M * alignmentCubeBase M t p (Q / M) ell - (t * (p + M * ell) - Q)| < M := by
  have ha := Int.emod_nonneg (t * p) hM.ne'
  have hb := Int.emod_lt_of_pos (t * p) hM
  have hc := Int.emod_nonneg Q hM.ne'
  have hd := Int.emod_lt_of_pos Q hM
  have he := alignmentCubeBase_reconstruction M t p (Q / M) ell
  have hf := Int.mul_ediv_add_emod Q M
  have hg : M * alignmentCubeBase M t p (Q / M) ell - (t * (p + M * ell) - Q) =
      Q % M - (t * p) % M := by linear_combination he - hf
  rw [hg, abs_lt]
  omega

theorem alignmentCubeBase_displacement_bound (M t p Q ell pivot : ℤ)
    (hM : 0 < M) (ht : 0 ≤ t) :
    |M * alignmentCubeBase M t p (Q / M) ell| ≤
      t * (|p - pivot| + |M * ell|) + |t * pivot - Q| + M := by
  have hr := (alignmentCubeBase_rounding_error M t p Q ell hM).le
  have hs : |p + M * ell - pivot| ≤ |p - pivot| + |M * ell| := by
    have he : p + M * ell - pivot = (p - pivot) + M * ell := by ring
    rw [he]
    exact abs_add_le _ _
  have hd : |t * (p + M * ell) - Q| ≤
      t * (|p - pivot| + |M * ell|) + |t * pivot - Q| := by
    calc
      _ = |t * (p + M * ell - pivot) + (t * pivot - Q)| := by congr 1; ring
      _ ≤ |t * (p + M * ell - pivot)| + |t * pivot - Q| := abs_add_le _ _
      _ = t * |p + M * ell - pivot| + |t * pivot - Q| := by rw [abs_mul, abs_of_nonneg ht]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hs ht) le_rfl
  calc
    _ ≤ |M * alignmentCubeBase M t p (Q / M) ell - (t * (p + M * ell) - Q)| +
        |t * (p + M * ell) - Q| := by
      simpa only [sub_add_cancel] using abs_add_le
        (M * alignmentCubeBase M t p (Q / M) ell - (t * (p + M * ell) - Q))
        (t * (p + M * ell) - Q)
    _ ≤ _ := by linarith

theorem alignmentCubeBase_scale_bound (M t p Q ell pivot a R C K : ℤ)
    (hM : 0 < M) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hK : 0 ≤ K) (htC : t ≤ C * a)
    (hp : |p - pivot| ≤ R) (hell : |M * ell| ≤ K * R)
    (hbin : |t * pivot - Q| ≤ a * R) :
    |M * alignmentCubeBase M t p (Q / M) ell| ≤
      (C * (K + 1) + 1) * a * R + M := by
  have h := alignmentCubeBase_displacement_bound M t p Q ell pivot hM ht
  have he : |p - pivot| + |M * ell| ≤ (K + 1) * R := by linarith
  have hf := mul_le_mul he htC ht (by positivity : 0 ≤ (K + 1) * R)
  nlinarith [hf]

theorem alignmentCubeBase_normalized_bound (M t p Q ell pivot a R C K : ℤ)
    (hM : 0 < M) (ht : 0 ≤ t) (hR : 0 ≤ R)
    (hK : 0 ≤ K) (htC : t ≤ C * a)
    (hp : |p - pivot| ≤ R) (hell : |M * ell| ≤ K * R)
    (hbin : |t * pivot - Q| ≤ a * R) :
    |(alignmentCubeBase M t p (Q / M) ell : ℝ)| ≤
      ((C : ℝ) * (K + 1) + 1) * ((a : ℝ) * R / M) + 1 := by
  have h := alignmentCubeBase_scale_bound M t p Q ell pivot a R C K
    hM ht hR hK htC hp hell hbin
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : |(M : ℝ) * alignmentCubeBase M t p (Q / M) ell| ≤
      ((C : ℝ) * (K + 1) + 1) * a * R + M := by exact_mod_cast h
  rw [abs_mul, abs_of_pos hm] at hb
  calc
    _ ≤ (((C : ℝ) * (K + 1) + 1) * a * R + M) / M :=
      (le_div_iff₀ hm).mpr (by nlinarith [hb])
    _ = _ := by field_simp

theorem alignmentCubeIncrement_scale_bound (M t ell a R C K : ℝ)
    (hM : 0 < M) (ht : 0 ≤ t) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (htC : t ≤ C * a) (hell : |M * ell| ≤ K * R) :
    |t * ell| ≤ C * K * (a * R / M) := by
  rw [abs_mul, abs_of_nonneg ht]
  rw [abs_mul, abs_of_pos hM] at hell
  have h := mul_le_mul hell htC ht (mul_nonneg hK hR)
  calc
    t * |ell| ≤ (C * K * (a * R)) / M := (le_div_iff₀ hM).mpr (by nlinarith [h])
    _ = _ := by ring

end Hindman168
