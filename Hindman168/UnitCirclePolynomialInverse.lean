import Hindman168.UnitCirclePolynomialFourierSelection
import Hindman168.ScalarPolynomialSimultaneousInverse
import Hindman168.UnitCircleStrongLinearRecurrence

namespace Hindman168
open Polynomial
open scoped BigOperators Classical Topology

/-- Genuine one-variable scalar polynomial inverse for all bounded unit
Lipschitz observables. One fixed bound precedes the polynomial, its arbitrary
real coefficients, N and observable; the SAME multiplier controls all original
nonconstant monomial coefficients. No mode or approximation is assumed. -/
theorem unit_circle_polynomial_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, 0 < N →
      ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCirclePolynomialDiscrepancy p N F‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ A ∧ ∀ i : ℕ, 0 < i → i ≤ D →
          (N : ℝ)^i*‖(((Q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨P, hP⟩ := unit_circle_finite_uniform_fourier_family (δ/8) (by positivity)
  let B : ℝ := 1+∑ c ∈ P, ∑ k ∈ c.support, ‖c k‖
  let K : ℕ := 1+∑ c ∈ P, ∑ k ∈ c.support, k.natAbs
  have hB : 0 < B := by dsimp only [B]; positivity
  have hK : 0 < K := by dsimp only [K]; omega
  have hbudget : ∀ c ∈ P, ∑ k ∈ c.support, ‖c k‖ ≤ B := by
    intro c hc
    have hh : (∑ k ∈ c.support, ‖c k‖) ≤ ∑ a ∈ P, ∑ k ∈ a.support, ‖a k‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun k _ => norm_nonneg (a k))) hc
    dsimp only [B]
    linarith
  have hfreq : ∀ c ∈ P, ∀ k ∈ c.support, k.natAbs ≤ K := by
    intro c hc k hk
    have h1 : k.natAbs ≤ ∑ j ∈ c.support, j.natAbs :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) hk
    have h2 : (∑ j ∈ c.support, j.natAbs) ≤ ∑ a ∈ P, ∑ j ∈ a.support, j.natAbs :=
      Finset.single_le_sum (f := fun a : ℤ →₀ ℂ => ∑ j ∈ a.support, j.natAbs)
        (fun a _ => Nat.zero_le _) hc
    dsimp only [K]
    omega
  let η := min (δ/(4*B)) (1/2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨A₀, hA₀, hinv⟩ := scalar_polynomial_phase_simultaneous_inverse D η hη hη1
  let A := A₀*K+1
  have hA : 0 < A := by dsimp only [A]; omega
  have hA₀A : A₀ ≤ A := by
    have hh := Nat.le_mul_of_pos_right A₀ hK
    dsimp only [A]
    omega
  refine ⟨A, hA, ?_⟩
  intro p hp N hN F hF hbad
  obtain ⟨c, hc, happrox⟩ := hP F hF
  let G : C(UnitAddCircle, ℂ) := c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))
  have htriangle : ‖unitCirclePolynomialDiscrepancy p N F‖ ≤
      ‖unitCirclePolynomialDiscrepancy p N G‖+2*‖F-G‖ := by
    calc
      _ = ‖unitCirclePolynomialDiscrepancy p N G+unitCirclePolynomialDiscrepancy p N (F-G)‖ := by
        rw [map_sub]
        congr 1
        abel
      _ ≤ ‖unitCirclePolynomialDiscrepancy p N G‖+‖unitCirclePolynomialDiscrepancy p N (F-G)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (unit_circle_polynomial_discrepancy_norm_bound p N (F-G))
  have hlarge : δ/2 ≤ ‖unitCirclePolynomialDiscrepancy p N G‖ := by
    change ‖F-G‖ < δ/8 at happrox
    linarith
  obtain ⟨k, hk, hk0, hkmean⟩ := unit_circle_polynomial_fourier_large_frequency p N hN c B δ
    hB hδ (hbudget c hc) hlarge
  have hscaled : (C (k : ℝ)*p).natDegree ≤ D := by
    have hh : (C (k : ℝ)*p).natDegree ≤ p.natDegree := by
      simpa only [natDegree_C, zero_add] using natDegree_mul_le (p := C (k : ℝ)) (q := p)
    exact hh.trans hp
  have hphase : η ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase (C (k : ℝ)*p))‖ := by
    rw [unit_circle_polynomial_nonzero_fourier_discrepancy p N k hk0] at hkmean
    exact (min_le_left _ _).trans hkmean
  obtain ⟨q, hq, hqA₀, hcoeff⟩ := hinv (C (k : ℝ)*p) hscaled N hN hphase
  let Q := q*k.natAbs
  have hQ : 0 < Q := Nat.mul_pos hq (Int.natAbs_pos.mpr hk0)
  have hQA : Q ≤ A :=
    (Nat.mul_le_mul hqA₀ (hfreq c hc k hk)).trans (by dsimp only [A]; omega)
  refine ⟨Q, hQ, hQA, ?_⟩
  intro i hi hiD
  have hb := hcoeff i hi hiD
  rw [coeff_C_mul] at hb
  have he : (Q : ℝ)*p.coeff i = (k.natAbs : ℝ)*((q : ℝ)*p.coeff i) := by
    dsimp only [Q]
    push_cast
    ring
  rw [he, unit_circle_nat_abs_multiplier_norm]
  have he' : (k : ℝ)*((q : ℝ)*p.coeff i) = (q : ℝ)*((k : ℝ)*p.coeff i) := by ring
  rw [he']
  exact hb.trans (by exact_mod_cast hA₀A)

end Hindman168
