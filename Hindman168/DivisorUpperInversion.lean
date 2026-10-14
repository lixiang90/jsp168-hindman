import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Möbius inversion above a divisor

Complementing divisors of a fixed nonzero integer turns an upper-divisor
sum into the ordinary divisor sum. This supplies the inverse transformation
needed to choose actual Selberg weights, rather than assume a small main term.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem upper_divisor_sum_complement {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P)
    (f : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then f (P / d) else 0) =
      ∑ k ∈ (P / l).divisors, f k := by
  rw [← Nat.sum_div_divisors P (fun d => if l ∣ d then f (P / d) else 0)]
  have he : ∀ k ∈ P.divisors,
      (if l ∣ P / k then f (P / (P / k)) else 0) =
        (if k ∣ P / l then f k else 0) := by
    intro k hk
    have hkP := Nat.dvd_of_mem_divisors hk
    rw [Nat.div_div_self hkP hP]
    have hi : l ∣ P / k ↔ k ∣ P / l := by
      rw [Nat.dvd_div_iff_mul_dvd hkP, Nat.dvd_div_iff_mul_dvd hl, Nat.mul_comm]
    simp only [hi]
  rw [Finset.sum_congr rfl he, ← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd hP (Nat.div_dvd_of_dvd hl)]

noncomputable def reverseDivisorMoebius (P : ℕ) (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) * y (P / x.2)

theorem reverseDivisorMoebius_sum (P : ℕ) (y : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ m.divisors, reverseDivisorMoebius P y k) = y (P / m) := by
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := reverseDivisorMoebius P y) (g := fun m => y (P / m))).mpr
    (fun _ _ => rfl)
  exact hi m hm

theorem upper_divisor_moebius_inversion {P l : ℕ} (hP : P ≠ 0) (hl : l ∣ P)
    (y : ℕ → ℝ) :
    (∑ d ∈ P.divisors, if l ∣ d then reverseDivisorMoebius P y (P / d) else 0) =
      y l := by
  rw [upper_divisor_sum_complement hP hl]
  have hlpos : 0 < l := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP hl)
  have hlle : l ≤ P := Nat.le_of_dvd (Nat.pos_of_ne_zero hP) hl
  rw [reverseDivisorMoebius_sum P y (Nat.div_pos hlle hlpos), Nat.div_div_self hl hP]

theorem reverseDivisorMoebius_at_top {P : ℕ} (hP : P ≠ 0) (y : ℕ → ℝ) :
    reverseDivisorMoebius P y P =
      ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) * y d := by
  rw [reverseDivisorMoebius,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (ArithmeticFunction.moebius a : ℝ) * y (P / b))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hP]

theorem reverseDivisorMoebius_eq_upper {P d : ℕ} (hP : P ≠ 0) (hd : d ∣ P)
    (y : ℕ → ℝ) :
    reverseDivisorMoebius P y (P / d) =
      ∑ l ∈ P.divisors, if d ∣ l then
        (ArithmeticFunction.moebius (l / d) : ℝ) * y l else 0 := by
  rw [reverseDivisorMoebius, Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℝ) * y (P / b))]
  calc
    _ = ∑ l ∈ P.divisors, if d ∣ l then
        (ArithmeticFunction.moebius ((P / d) / (P / l)) : ℝ) *
          y (P / (P / l)) else 0 :=
      (upper_divisor_sum_complement hP hd _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hquot : (P / d) / (P / l) = l / d := by
        calc
          _ = (P / (P / l)) / d := by
            rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
          _ = _ := by rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hl) hP]
      rw [hquot, Nat.div_div_self (Nat.dvd_of_mem_divisors hl) hP]

end Hindman168
