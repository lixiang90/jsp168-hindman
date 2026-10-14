import Hindman168.RoughPrimeEvents

/-!
# Constant and empty-tuple base cases for dyadic rough coprimality

A prime dividing a nonzero fixed integer is at most its natural absolute
value. Once w exceeds this fixed value, the common-prime event is empty,
under every pair of sampling laws and every choice of dyadic endpoints.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem prime_le_integer_natAbs_of_dvd {q : ℕ} (_hq : q.Prime) {c : ℤ}
    (hc : c ≠ 0) (hqc : (q : ℤ) ∣ c) : q ≤ c.natAbs :=
  Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (Int.natCast_dvd.mp hqc)

theorem commonPrimeEvent_zero_left {m n w : ℕ} (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : ¬ commonPrimeEvent w 0 G xy := by
  simp only [commonPrimeEvent, map_zero, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem commonPrimeEvent_zero_right {m n w : ℕ} (F : MvPolynomial (Fin m) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : ¬ commonPrimeEvent w F 0 xy := by
  simp only [commonPrimeEvent, map_zero, ne_eq, not_true_eq_false, false_and, and_false,
    not_false_eq_true]

theorem commonPrimeEvent_constant_left {m n w : ℕ} (c : ℤ)
    (hcw : c.natAbs ≤ w) (G : MvPolynomial (Fin n) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : ¬ commonPrimeEvent w (MvPolynomial.C c) G xy := by
  rintro ⟨hc, _, q, hq, hwq, hqc, _⟩
  simp only [MvPolynomial.eval_C] at hc hqc
  exact hwq.not_ge ((prime_le_integer_natAbs_of_dvd hq hc hqc).trans hcw)

theorem commonPrimeEvent_constant_right {m n w : ℕ} (c : ℤ)
    (hcw : c.natAbs ≤ w) (F : MvPolynomial (Fin m) ℤ)
    (xy : (Fin m → ℕ) × (Fin n → ℕ)) : ¬ commonPrimeEvent w F (MvPolynomial.C c) xy := by
  rw [commonPrimeEvent_swap]
  exact commonPrimeEvent_constant_left c hcw F xy.swap

theorem commonPrimeEvent_empty_tuple_left {n w : ℕ}
    (F : MvPolynomial (Fin 0) ℤ) (G : MvPolynomial (Fin n) ℤ)
    (hw : (F.coeff 0).natAbs ≤ w) (xy : (Fin 0 → ℕ) × (Fin n → ℕ)) :
    ¬ commonPrimeEvent w F G xy := by
  rw [F.eq_C_of_isEmpty]
  exact commonPrimeEvent_constant_left _ hw G xy

theorem commonPrimeEvent_constant_event_zero {m n w : ℕ} (c : ℤ)
    (hw : c.natAbs ≤ w) (G : MvPolynomial (Fin n) ℤ)
    (μ : Mass (Fin m → ℕ)) (ν : Mass (Fin n → ℕ)) :
    event (tensor μ ν) (commonPrimeEvent w (MvPolynomial.C c) G) = 0 := by
  have hE : commonPrimeEvent (m := m) w (MvPolynomial.C c) G = (fun _ => False) := by
    funext xy
    exact propext ⟨commonPrimeEvent_constant_left c hw G xy, fun h => False.elim h⟩
  rw [hE, event_false]

end Hindman168
