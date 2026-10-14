import Hindman168.ScalarPolynomialLinearPhaseInverse
import Hindman168.FiniteBoundedCandidateDensity
import Hindman168.UnitCircleDensePowerInverse

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

/-- Genuine fixed-data Weyl leading-coefficient inverse for every positive
degree bound. The induction uses actual dense nonzero differences on their
actual remaining intervals, followed by genuine strong linear recurrence.
No per-polynomial character, multiplier or recurrence existence is assumed. -/
theorem scalar_polynomial_phase_leading_inverse (d : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : ℝ[X], p.natDegree ≤ d+1 → ∀ N : ℕ, 0 < N →
      δ ≤ ‖finiteComplexSetMean (Finset.range N) (scalarPolynomialPhase p)‖ →
      ∃ q : ℕ, 0 < q ∧ q ≤ A ∧
        (N : ℝ)^(d+1)*‖(((q : ℝ)*p.coeff (d+1) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  induction d generalizing δ with
  | zero =>
    simpa only [zero_add, pow_one] using scalar_polynomial_linear_phase_inverse δ hδ
  | succ d ih =>
    let τ := δ^2/8
    have hτ : 0 < τ := by dsimp only [τ]; positivity
    have hτ1 : τ ≤ 1 := by dsimp only [τ]; nlinarith
    obtain ⟨B, hB, hind⟩ := ih τ hτ hτ1
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    let μ := τ/(B : ℝ)
    have hμ : 0 < μ := div_pos hτ hBr
    have hμ1 : μ ≤ 1 := by
      apply (div_le_iff₀ hBr).mpr
      have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
      linarith
    let C := (B : ℝ)/τ^(d+1)+1
    have hC : 0 < C := by dsimp only [C]; positivity
    have hBC : (B : ℝ)/τ^(d+1) ≤ C := by dsimp only [C]; linarith
    obtain ⟨K, M₀, hK, hM₀, hpower⟩ := unit_circle_dense_multiple_power_inverse μ hμ hμ1
      (d+1) (by omega) C hC
    let M := M₀+⌈4/δ^2⌉₊+1
    let A := K*B*(d+2)+⌈(K : ℝ)*C⌉₊+M^(d+2)+1
    have hM : 0 < M := by dsimp only [M]; omega
    have hA : 0 < A := by dsimp only [A]; omega
    have hMA : M^(d+2) ≤ A := by dsimp only [A]; omega
    have hKA : K*B*(d+2) ≤ A := by dsimp only [A]; omega
    have hKCA : (K : ℝ)*C ≤ A := (Nat.le_ceil _).trans (by
      exact_mod_cast (show ⌈(K : ℝ)*C⌉₊ ≤ A by dsimp only [A]; omega))
    refine ⟨A, hA, ?_⟩
    intro p hp N hN hmean
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    by_cases hMN : M ≤ N
    · have hMNr : (M : ℝ) ≤ N := by exact_mod_cast hMN
      have h4 : 4/δ^2 ≤ M := (Nat.le_ceil _).trans (by
        exact_mod_cast (show ⌈4/δ^2⌉₊ ≤ M by dsimp only [M]; omega))
      have hlarge : 4 ≤ δ^2*(N : ℝ) := by
        have hh := (div_le_iff₀ (by positivity : 0 < δ^2)).mp (h4.trans hMNr)
        nlinarith
      obtain ⟨T, hT, hdiff⟩ := scalar_polynomial_dense_difference_means p N hN δ hδ hlarge hmean
      let R := fun q h : ℕ =>
        ‖(((h : ℝ)*((q : ℝ)*(d+2 : ℕ)*p.coeff (d+2)) : ℝ) : UnitAddCircle)‖ ≤
          C/(N : ℝ)^(d+1)
      have hR : ∀ h ∈ T, ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ R q h := by
        intro h hh
        obtain ⟨hpos, hlt, hrem, hlen, hmean'⟩ := hdiff h hh
        obtain ⟨q, hq, hqB, hbound⟩ := hind
          (scalarPolynomialDifference p (h : ℝ))
          (scalar_polynomial_difference_degree_le p (h : ℝ) (d+1) hp)
          (N-h) hrem hmean'
        rw [scalar_polynomial_difference_top_coefficient p (h : ℝ) (d+1) hp] at hbound
        have he : (q : ℝ)*((d+1+1 : ℕ)* (h : ℝ)*p.coeff (d+1+1)) =
            (h : ℝ)*((q : ℝ)*(d+2 : ℕ)*p.coeff (d+2)) := by
          rw [show d+1+1=d+2 by omega]
          ring
        rw [he] at hbound
        have hscaled := real_power_bound_from_fractional_length τ (N-h : ℕ) (N : ℝ)
          ‖(((h : ℝ)*((q : ℝ)*(d+2 : ℕ)*p.coeff (d+2)) : ℝ) : UnitAddCircle)‖
          (B : ℝ) (d+1) hτ hNr.le (norm_nonneg _) hlen hbound
        refine ⟨q, hq, hqB, ?_⟩
        apply (le_div_iff₀ (pow_pos hNr (d+1))).mpr
        nlinarith only [hscaled, hBC]
      obtain ⟨q, hq, hqB, hcommon⟩ := finite_bounded_candidate_density T B hB R hR
      have hTS : T.filter (R q) ⊆ (Finset.range N).filter (fun h : ℕ => R q h) := by
        intro h hh
        have hv := Finset.mem_filter.mp hh
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hdiff h hv.1).2.1, hv.2⟩
      have hcard : ((T.filter (R q)).card : ℝ) ≤
          (((Finset.range N).filter (fun h : ℕ => R q h)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hTS
      have hdense : μ*(N : ℝ) ≤ ((Finset.range N).filter (fun h : ℕ => R q h)).card := by
        have hd := div_le_div_of_nonneg_right hT hBr.le
        have he : (δ^2/8*(N : ℝ))/(B : ℝ) = μ*(N : ℝ) := by dsimp only [μ, τ]; ring
        rw [he] at hd
        exact hd.trans (hcommon.trans hcard)
      have hM₀N : M₀ ≤ N := by dsimp only [M] at hMN; omega
      obtain ⟨q', hq', hq'K, htop⟩ := hpower
        ((q : ℝ)*(d+2 : ℕ)*p.coeff (d+2)) N hM₀N hdense
      let Q := q'*q*(d+2)
      have hQ : 0 < Q := by dsimp only [Q]; positivity
      have hQA : Q ≤ A := by
        have hmul := Nat.mul_le_mul (Nat.mul_le_mul hq'K hqB) (le_refl (d+2))
        exact hmul.trans hKA
      have he : (Q : ℝ)*p.coeff (d+2) =
          (q' : ℝ)*((q : ℝ)*(d+2 : ℕ)*p.coeff (d+2)) := by
        dsimp only [Q]
        push_cast
        ring
      refine ⟨Q, hQ, hQA, ?_⟩
      rw [he]
      exact htop.trans hKCA
    · have hNM : (N : ℝ) ≤ M := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hMN))
      have hpow : (N : ℝ)^(d+2) ≤ (M : ℝ)^(d+2) := pow_le_pow_left₀ hNr.le hNM _
      have hnorm : ‖((p.coeff (d+2) : ℝ) : UnitAddCircle)‖ ≤ 1 := by
        have hh := AddCircle.norm_le_half_period (1 : ℝ) (x := ((p.coeff (d+2) : ℝ) : UnitAddCircle))
          (by norm_num)
        norm_num at hh
        linarith
      have hb : (N : ℝ)^(d+2)*‖((p.coeff (d+2) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
        calc
          _ ≤ (N : ℝ)^(d+2) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (pow_nonneg hNr.le _)
          _ ≤ (M : ℝ)^(d+2) := hpow
          _ ≤ A := by exact_mod_cast hMA
      exact ⟨1, by omega, hA, by simpa only [Nat.cast_one, one_mul] using hb⟩

end Hindman168
