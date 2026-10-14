import Hindman168.FiniteVectorPolynomialDegree
import Hindman168.NativeLieRationalProductCurve

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

theorem nativeLieRationalDefectPolynomial_degree {p q : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q e) :
    finiteVectorPolynomialDegreeLE (nativeLieRationalDefectPolynomial (I := I) (G := G) p q)
      (Group.nilpotencyClass G * d + e) := by
  apply finiteVectorPolynomialDegreeLE_sum
  intro j hj
  apply finiteVectorPolynomialDegreeLE_scale
  apply finiteVectorPolynomialDegreeLE_mono (finiteVectorPolynomialDegreeLE_adPower _ hp hq (j + 1))
  exact Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega)) e

theorem nativeLieRationalDefectPowerPolynomial_degree {p q : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q e) (n : ℕ) :
    finiteVectorPolynomialDegreeLE (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q n)
      (n * (Group.nilpotencyClass G * d) + e) := by
  induction n with
  | zero => simpa only [nativeLieRationalDefectPowerPolynomial, zero_mul, zero_add] using hq
  | succ n ih =>
    have h := nativeLieRationalDefectPolynomial_degree (I := I) (G := G) hp ih
    simpa only [nativeLieRationalDefectPowerPolynomial, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm] using h

theorem nativeLieRationalFieldPolynomial_degree {p q : List (ℕ × E)} {d e : ℕ}
    (hp : finiteVectorPolynomialDegreeLE p d) (hq : finiteVectorPolynomialDegreeLE q e) :
    finiteVectorPolynomialDegreeLE (nativeLieRationalFieldPolynomial (I := I) (G := G) p q)
      (Group.nilpotencyClass G * (Group.nilpotencyClass G * d) + e) := by
  apply finiteVectorPolynomialDegreeLE_sum
  intro j hj
  apply finiteVectorPolynomialDegreeLE_mono (nativeLieRationalDefectPowerPolynomial_degree (I := I) (G := G) hp hq j)
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hj)) e

theorem nativeLieRationalPicardPolynomial_degree (w u : E) (n : ℕ) :
    finiteVectorPolynomialDegreeLE (nativeLieRationalPicardPolynomial (I := I) (G := G) w u n)
      ((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^ n) := by
  induction n with
  | zero =>
    exact finiteVectorPolynomialDegreeLE_mono (finiteVectorPolynomialDegreeLE_singleton u 0) (Nat.zero_le _)
  | succ n ih =>
    have hf := nativeLieRationalFieldPolynomial_degree (I := I) (G := G) ih
      (finiteVectorPolynomialDegreeLE_singleton w 0)
    have hp := finiteVectorPolynomialDegreeLE_primitive hf
    have hb := finiteVectorPolynomialDegreeLE_append
      (finiteVectorPolynomialDegreeLE_mono (finiteVectorPolynomialDegreeLE_singleton u 0) (Nat.zero_le _)) hp
    apply finiteVectorPolynomialDegreeLE_mono hb
    have hpow : 1 ≤ (Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^ n :=
      Nat.one_le_pow n _ (by omega)
    rw [pow_succ]
    nlinarith

theorem nativeLieRationalProductPolynomial_degree (u w : E) :
    finiteVectorPolynomialDegreeLE (nativeLieRationalProductPolynomial (I := I) (G := G) u w)
      ((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^ (Group.nilpotencyClass G + 1)) :=
  nativeLieRationalPicardPolynomial_degree (I := I) (G := G) w u _

end Hindman168
