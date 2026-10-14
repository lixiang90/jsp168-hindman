import Hindman168.MasterPredictionOriginalCubeLimit
import Hindman168.IntegerPolynomialValueBounds
import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Concrete quotient lengths and replica polynomial modulus caps

Only variables that actually occur in a replica polynomial need a size
bound. This permits independent replicas assigned to different gaps.
The actual original interval length is the natural quotient R/(J|M_q|).
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem roughPartNat_dvd_value (w n : ℕ) : roughPartNat w n ∣ n := by
  by_cases hn : n = 0
  · simp [hn, roughPartNat]
  · rw [roughPartNat, if_neg hn]
    have hd : (n.primeFactorsList.filter (fun p => decide (w < p))).prod ∣ n.primeFactorsList.prod :=
      List.Sublist.prod_dvd_prod List.filter_sublist
    simpa only [Nat.prod_primeFactorsList hn] using hd

theorem roughPartNat_le_value (w n : ℕ) : roughPartNat w n ≤ n := by
  by_cases hn : n = 0
  · simp [hn, roughPartNat]
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (roughPartNat_dvd_value w n)

theorem integerPolynomial_eval_natAbs_le_on_vars {σ : Type*} (f : MvPolynomial σ ℤ)
    (x : σ → ℤ) {B : ℕ} (hB : 1 ≤ B)
    (hx : ∀ i ∈ f.vars, (x i).natAbs ≤ B) :
    (MvPolynomial.eval x f).natAbs ≤ integerPolynomialCoeffSize f * B ^ f.totalDegree := by
  rw [MvPolynomial.eval_eq]
  calc
    _ ≤ ∑ d ∈ f.support, (f.coeff d * ∏ i ∈ d.support, x i ^ d i).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ d ∈ f.support, (f.coeff d).natAbs * B ^ f.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Int.natAbs_mul, integer_natAbs_finsetProd]
      simp only [Int.natAbs_pow]
      apply Nat.mul_le_mul_left
      calc
        _ ≤ ∏ i ∈ d.support, B ^ d i := Finset.prod_le_prod' (fun i hi =>
          Nat.pow_le_pow_left (hx i ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)) (d i))
        _ = B ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ B ^ f.totalDegree := Nat.pow_le_pow_right (by omega) (MvPolynomial.le_totalDegree hd)
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem predictionCubeModulus_natAbs {r : ℕ} (w s : ℕ)
    (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) :
    (predictionCubeModulus w s f x).natAbs =
      s * roughPartNat w (MvPolynomial.eval (fun j => (x j : ℤ)) f).natAbs := by
  simp only [predictionCubeModulus, Int.natAbs_mul, Int.natAbs_natCast]

theorem predictionCubeModulus_W_divisible {r : ℕ} (w s : ℕ)
    (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) (hs : primorial w ∣ s) :
    (primorial w : ℤ) ∣ predictionCubeModulus w s f x :=
  (Int.natCast_dvd.mpr hs).trans (dvd_mul_right _ _)

theorem predictionCubeModulus_nonzero {r : ℕ} (w s : ℕ)
    (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) (hs : 0 < s)
    (hf : MvPolynomial.eval (fun j => (x j : ℤ)) f ≠ 0) :
    predictionCubeModulus w s f x ≠ 0 := by
  have hr := roughPartNat_pos (w := w) (Int.natAbs_ne_zero.mpr hf)
  exact mul_ne_zero (by exact_mod_cast hs.ne') (by exact_mod_cast hr.ne')

theorem predictionCubeModulus_polynomial_cap {r : ℕ} (w s J B : ℕ)
    (f : MvPolynomial (Fin r) ℤ) (x : Fin r → ℕ) (hB : 2 ≤ B) (hs : s ≤ B)
    (hx : ∀ j ∈ f.vars, x j ≤ B) :
    J * (predictionCubeModulus w s f x).natAbs ≤
      B ^ (J + integerPolynomialCoeffSize f + f.totalDegree + 1) := by
  let C := integerPolynomialCoeffSize f
  have hJ : J ≤ B ^ J := (show J < 2 ^ J from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hB J)
  have hC : C ≤ B ^ C := (show C < 2 ^ C from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hB C)
  have he := integerPolynomial_eval_natAbs_le_on_vars f (fun j => (x j : ℤ))
    (B := B) (by omega) (fun j hj => by simpa only [Int.natAbs_natCast] using hx j hj)
  rw [predictionCubeModulus_natAbs]
  calc
    _ ≤ J * (s * (C * B ^ f.totalDegree)) := Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left _ ((roughPartNat_le_value _ _).trans he))
    _ ≤ B ^ J * (B * (B ^ C * B ^ f.totalDegree)) :=
      Nat.mul_le_mul hJ (Nat.mul_le_mul hs (Nat.mul_le_mul_right _ hC))
    _ = _ := by simp only [C, pow_add, pow_one]; ring

noncomputable def predictionQuotientLength {N r b : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin b → Fin N) (J : ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (w : ℕ) (x : Fin r → ℕ) (q : Fin b) : ℕ :=
  F.gap w (gap w q).val / (J * (predictionCubeModulus w (s w q) (f q) x).natAbs)

theorem predictionQuotientLength_lower {N r b : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin b → Fin N) (J : ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (w : ℕ) (x : Fin r → ℕ) (q : Fin b) (k : ℕ) (hJ : 0 < J)
    (hM : predictionCubeModulus w (s w q) (f q) x ≠ 0)
    (hcap : J * (predictionCubeModulus w (s w q) (f q) x).natAbs ≤
      ((F.pool w (gap w q).val).upper + F.auxiliary w (gap w q).val) ^ k) :
    masterShiftLengthLowerBound F w (gap w q).val k ≤ predictionQuotientLength F gap J s f w x q :=
  masterShiftLengthLowerBound_le_actual F w _ k J _
    (Nat.mul_pos hJ (Int.natAbs_pos.mpr hM)) hcap

theorem predictionQuotientLength_displacement {N r b : ℕ}
    (F : MasterParameterFamily) (gap : ℕ → Fin b → Fin N) (J : ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (w : ℕ) (x : Fin r → ℕ) (q : Fin b) (hJ : 1 ≤ J) :
    |(predictionCubeModulus w (s w q) (f q) x : ℝ)| * predictionQuotientLength F gap J s f w x q ≤
      F.gap w (gap w q).val := by
  have hb := actual_shift_modulus_length_bound (F.gap w (gap w q).val) J
    (predictionCubeModulus w (s w q) (f q) x).natAbs hJ
  have ha : ((predictionCubeModulus w (s w q) (f q) x).natAbs : ℝ) =
      |(predictionCubeModulus w (s w q) (f q) x : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (predictionCubeModulus w (s w q) (f q) x))
  rw [← ha]
  exact_mod_cast hb

end Hindman168
