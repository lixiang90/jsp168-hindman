import Hindman168.LeibmanDenseMonomialSpan
import Hindman168.FiniteRationalCoordinateReconstruction
import Hindman168.IntegerCombinationModOneBound

namespace Hindman168
open scoped BigOperators Classical

theorem leibman_dense_direction_integer_reconstruction {n : ℕ}
    (I : Finset (Fin n → ℕ)) (d : ℕ) (hd : ∀ i ∈ I, (∑ j, i j) ≤ d)
    (L : ℕ) (hL : 0 < L) :
    ∃ B : ℕ, 0 < B ∧ ∀ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) →
      d*L^n < T.card*L →
      ∃ D : ℕ, 0 < D ∧ D ≤ B ∧ ∃ m : ↥I → ↥T → ℤ,
        (∀ i, ∑ t : ↥T, (m i t).natAbs ≤ B) ∧
        ∀ i j, ∑ t : ↥T, (m i t : ℚ)*
          leibmanMonomialVector I (fun k => (t.val k : ℚ)) j = if j=i then (D : ℚ) else 0 := by
  obtain ⟨B, hB, hbound⟩ := finite_rational_reconstruction_uniform_bound
    (Fintype.piFinset (fun _ : Fin n => Finset.range L))
    (fun x : Fin n → ℕ => leibmanMonomialVector I (fun k => (x k : ℚ)))
  refine ⟨B, hB, ?_⟩
  intro T hT hdense
  obtain ⟨D, hD, hDB, m, hm, he⟩ := hbound T hT
    (leibman_dense_integer_directions_span I d hd L hL T hT hdense)
  refine ⟨D, hD, hDB, m, hm, ?_⟩
  intro i j
  have h := he i j
  by_cases hj : j=i
  · simpa only [if_pos hj] using h
  · simpa only [if_neg hj] using h

theorem leibman_direction_real_coefficient_identity {n : ℕ}
    (I : Finset (Fin n → ℕ)) (T : Finset (Fin n → ℕ)) (D : ℕ) (m : ↥I → ↥T → ℤ)
    (hm : ∀ i j, ∑ t : ↥T, (m i t : ℚ)*
      leibmanMonomialVector I (fun k => (t.val k : ℚ)) j = if j=i then (D : ℚ) else 0)
    (a : ↥I → ℝ) (i : ↥I) :
    (D : ℝ)*a i = ∑ t : ↥T, (m i t : ℝ)*
      (∑ j : ↥I, a j*leibmanMonomialVector I (fun k => (t.val k : ℝ)) j) := by
  have hr (j : ↥I) : ∑ t : ↥T, (m i t : ℝ)*
      leibmanMonomialVector I (fun k => (t.val k : ℝ)) j = if j=i then (D : ℝ) else 0 := by
    have h := hm i j
    unfold leibmanMonomialVector at h ⊢
    have hreal := congrArg (fun r : ℚ => (r : ℝ)) h
    push_cast at hreal
    by_cases hj : j=i
    · simpa only [if_pos hj, Rat.cast_natCast] using hreal
    · simpa only [if_neg hj, Rat.cast_zero] using hreal
  symm
  calc
    _ = ∑ j : ↥I, a j*(∑ t : ↥T, (m i t : ℝ)*
        leibmanMonomialVector I (fun k => (t.val k : ℝ)) j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      simp only [hr, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

theorem leibman_dense_direction_modular_coefficient_bound {n : ℕ}
    (I : Finset (Fin n → ℕ)) (d : ℕ) (hd : ∀ i ∈ I, (∑ j, i j) ≤ d)
    (L : ℕ) (hL : 0 < L) :
    ∃ B : ℕ, 0 < B ∧ ∀ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) → d*L^n < T.card*L →
      ∃ D : ℕ, 0 < D ∧ D ≤ B ∧ ∀ (a : ↥I → ℝ) (eps : ℝ), 0 ≤ eps →
        (∀ t : ↥T, ‖((∑ j : ↥I, a j*
          leibmanMonomialVector I (fun k => (t.val k : ℝ)) j : ℝ) : UnitAddCircle)‖ ≤ eps) →
        ∀ i, ‖(((D : ℝ)*a i : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*eps := by
  obtain ⟨B, hB, hbound⟩ := leibman_dense_direction_integer_reconstruction I d hd L hL
  refine ⟨B, hB, ?_⟩
  intro T hT hdense
  obtain ⟨D, hD, hDB, m, hbudget, hm⟩ := hbound T hT hdense
  refine ⟨D, hD, hDB, ?_⟩
  intro a eps heps hvalues i
  rw [leibman_direction_real_coefficient_identity I T D m hm a i]
  exact (integer_combination_mod_one_bound (m i)
    (fun t => ∑ j : ↥I, a j*leibmanMonomialVector I (fun k => (t.val k : ℝ)) j)
    eps hvalues).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hbudget i) heps)

theorem leibman_direction_density_card_condition {n : ℕ} (d L : ℕ) (hL : 0 < L)
    (T : Finset (Fin n → ℕ)) (eps : ℝ) (hsize : (d : ℝ) < eps*L)
    (hdense : eps*(L : ℝ)^n ≤ T.card) : d*L^n < T.card*L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h : (d : ℝ)*(L : ℝ)^n < (T.card : ℝ)*L := by
    calc
      _ < (eps*L)*(L : ℝ)^n := mul_lt_mul_of_pos_right hsize (pow_pos hLr n)
      _ = (eps*(L : ℝ)^n)*L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdense hLr.le
  exact_mod_cast h

end Hindman168
