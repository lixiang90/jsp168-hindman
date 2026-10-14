import Mathlib.Algebra.MvPolynomial.SchwartzZippel

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem leibman_polynomial_zero_card_mul {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (S : Finset K) (hS : S.Nonempty) :
    ((Fintype.piFinset (fun _ : Fin n => S)).filter (fun x => eval x p = 0)).card*S.card ≤
      p.totalDegree*S.card^n := by
  have hz := schwartz_zippel_totalDegree hp S
  have hs : (0 : ℚ≥0) < S.card := by exact_mod_cast hS.card_pos
  have h := (div_le_div_iff₀ (pow_pos hs n) hs).mp hz
  exact_mod_cast h

theorem leibman_polynomial_eq_zero_of_dense_zeros {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} (p : MvPolynomial (Fin n) K) (d : ℕ) (hd : p.totalDegree ≤ d)
    (S : Finset K) (hS : S.Nonempty) (T : Finset (Fin n → K))
    (hT : T ⊆ Fintype.piFinset (fun _ : Fin n => S))
    (hdense : d*S.card^n < T.card*S.card) (hzero : ∀ x ∈ T, eval x p = 0) : p = 0 := by
  by_contra hp
  have hsub : T ⊆ (Fintype.piFinset (fun _ : Fin n => S)).filter (fun x => eval x p = 0) :=
    fun x hx => Finset.mem_filter.mpr ⟨hT hx, hzero x hx⟩
  have hcount := leibman_polynomial_zero_card_mul p hp S hS
  have hle := (Nat.mul_le_mul_right S.card (Finset.card_le_card hsub)).trans
    (hcount.trans (Nat.mul_le_mul_right (S.card^n) hd))
  exact (not_lt_of_ge hle) hdense

end Hindman168
