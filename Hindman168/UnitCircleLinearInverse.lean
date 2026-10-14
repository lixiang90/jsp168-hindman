import Hindman168.UnitCircleOrbitDiscrepancy

namespace Hindman168
open scoped BigOperators Classical Topology

theorem unit_circle_fourier_polynomial_large_frequency (x : ℝ) (N : ℕ) (hN : 0 < N)
    (c : ℤ →₀ ℂ) (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    (hbudget : ∑ k ∈ c.support, ‖c k‖ ≤ B)
    (hlarge : δ/2 ≤ ‖unitCircleOrbitDiscrepancy x N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖) :
    ∃ k ∈ c.support, k ≠ 0 ∧ δ/(4*B) ≤ ‖unitCircleOrbitDiscrepancy x N (fourier k)‖ := by
  by_contra! h
  have hphase : ∀ k ∈ c.support, ‖unitCircleOrbitDiscrepancy x N (fourier k)‖ ≤ δ/(4*B) := by
    intro k hk
    by_cases hz : k=0
    · rw [hz, unit_circle_zero_fourier_discrepancy x N hN, norm_zero]
      positivity
    · exact (h k hk hz).le
  have heq : unitCircleOrbitDiscrepancy x N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))) =
      ∑ k ∈ c.support, c k*unitCircleOrbitDiscrepancy x N (fourier k) := by
    rw [Finsupp.sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hb : ‖unitCircleOrbitDiscrepancy x N
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖ ≤ δ/4 := by
    rw [heq]
    calc
      _ ≤ ∑ k ∈ c.support, ‖c k*unitCircleOrbitDiscrepancy x N (fourier k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ c.support, ‖c k‖*(δ/(4*B)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hphase k hk) (norm_nonneg _)
      _ = (∑ k ∈ c.support, ‖c k‖)*(δ/(4*B)) := by rw [Finset.sum_mul]
      _ ≤ B*(δ/(4*B)) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = δ/4 := by field_simp
  linarith

/-- Genuine scalar linear torus inverse, with one fixed bound depending only
on delta. No per-orbit character existence or Fourier approximation is assumed.
Only fixed-data bounds are asserted, not polynomial dependence on delta. -/
theorem unit_circle_linear_inverse (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (x : ℝ) (N : ℕ), 0 < N →
      ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖unitCircleOrbitDiscrepancy x N F‖ →
        ∃ k : ℤ, 0 < k.natAbs ∧ k.natAbs ≤ A ∧
          (N : ℝ)*‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨P, hP⟩ := unit_circle_finite_uniform_fourier_family (δ/8) (by positivity)
  let B : ℝ := 1+∑ c ∈ P, ∑ k ∈ c.support, ‖c k‖
  let K : ℕ := 1+∑ c ∈ P, ∑ k ∈ c.support, k.natAbs
  let A : ℕ := K+⌈2*B/δ⌉₊+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hbudget : ∀ c ∈ P, ∑ k ∈ c.support, ‖c k‖ ≤ B := by
    intro c hc
    have h : (∑ k ∈ c.support, ‖c k‖) ≤ ∑ a ∈ P, ∑ k ∈ a.support, ‖a k‖ :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun k _ => norm_nonneg (a k))) hc
    dsimp only [B]
    linarith
  have hfreq : ∀ c ∈ P, ∀ k ∈ c.support, k.natAbs ≤ K := by
    intro c hc k hk
    have h1 : k.natAbs ≤ ∑ j ∈ c.support, j.natAbs := Finset.single_le_sum (fun j _ => Nat.zero_le _) hk
    have h2 : (∑ j ∈ c.support, j.natAbs) ≤ ∑ a ∈ P, ∑ j ∈ a.support, j.natAbs :=
      Finset.single_le_sum (f := fun a : ℤ →₀ ℂ => ∑ j ∈ a.support, j.natAbs)
        (fun a _ => Nat.zero_le _) hc
    dsimp only [K]
    omega
  refine ⟨A, by dsimp only [A]; omega, ?_⟩
  intro x N hN F hF hbad
  obtain ⟨c, hc, happrox⟩ := hP F hF
  let G : C(UnitAddCircle, ℂ) := c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))
  have htriangle : ‖unitCircleOrbitDiscrepancy x N F‖ ≤
      ‖unitCircleOrbitDiscrepancy x N G‖+2*‖F-G‖ := by
    calc
      _ = ‖unitCircleOrbitDiscrepancy x N G+unitCircleOrbitDiscrepancy x N (F-G)‖ := by
        rw [map_sub]
        congr 1
        abel
      _ ≤ ‖unitCircleOrbitDiscrepancy x N G‖+‖unitCircleOrbitDiscrepancy x N (F-G)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (unit_circle_orbit_discrepancy_norm_bound x N (F-G))
  have hlarge : δ/2 ≤ ‖unitCircleOrbitDiscrepancy x N G‖ := by
    change ‖F-G‖ < δ/8 at happrox
    linarith
  obtain ⟨k, hk, hk0, hklarge⟩ := unit_circle_fourier_polynomial_large_frequency x N hN c B δ
    hB hδ (hbudget c hc) hlarge
  have hinv := unit_circle_large_linear_mean_inverse ((k : ℝ)*x) N hN (δ/(4*B))
    (by positivity) (by simpa only [unit_circle_nonzero_fourier_discrepancy x N k hk0] using hklarge)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (N : ℝ)*(1/(2*(δ/(4*B))*(N : ℝ))) = 2*B/δ := by field_simp; ring
  have hnorm : (N : ℝ)*‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ 2*B/δ := by
    simpa only [heq] using mul_le_mul_of_nonneg_left hinv hNr.le
  refine ⟨k, Int.natAbs_pos.mpr hk0, (hfreq c hc k hk).trans ?_, hnorm.trans ?_⟩
  · dsimp only [A]
    omega
  · refine (Nat.le_ceil (2*B/δ)).trans ?_
    exact_mod_cast (show ⌈2*B/δ⌉₊ ≤ A by dsimp only [A]; omega)

/-- The same genuine uniform inverse applies to arbitrary affine circle
orbits, by true Haar translation invariance. -/
theorem unit_circle_affine_linear_inverse (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ, 0 < A ∧ ∀ (x b : ℝ) (N : ℕ), 0 < N →
      ∀ F ∈ unitLipschitzObservables UnitAddCircle,
        δ ≤ ‖finiteComplexSetMean (Finset.range N)
          (fun n => F (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) -
            ∫ t, F t ∂AddCircle.haarAddCircle‖ →
        ∃ k : ℤ, 0 < k.natAbs ∧ k.natAbs ≤ A ∧
          (N : ℝ)*‖(((k : ℝ)*x : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ) := by
  obtain ⟨A, hA, hinv⟩ := unit_circle_linear_inverse δ hδ
  refine ⟨A, hA, ?_⟩
  intro x b N hN F hF hbad
  let G : C(UnitAddCircle, ℂ) := ⟨fun t => F ((b : UnitAddCircle)+t), by fun_prop⟩
  have hG : G ∈ unitLipschitzObservables UnitAddCircle := by
    refine ⟨?_, fun t => hF.2 _⟩
    change LipschitzWith 1 (fun t : UnitAddCircle => F ((b : UnitAddCircle)+t))
    simpa only [one_mul, Function.comp_def] using
      hF.1.comp (isometry_add_left (b : UnitAddCircle)).lipschitz
  have heq : unitCircleOrbitDiscrepancy x N G = finiteComplexSetMean (Finset.range N)
      (fun n => F (((b+(n : ℝ)*x : ℝ) : UnitAddCircle))) -
        ∫ t, F t ∂AddCircle.haarAddCircle := by
    rw [unit_circle_orbit_discrepancy_apply]
    have hi : (∫ t, G t ∂AddCircle.haarAddCircle) =
        ∫ t, F t ∂AddCircle.haarAddCircle :=
      MeasureTheory.integral_add_left_eq_self F (b : UnitAddCircle)
    change finiteComplexSetMean (Finset.range N) (fun n =>
      F ((b : UnitAddCircle)+(((n : ℝ)*x : ℝ) : UnitAddCircle))) - _ = _
    rw [hi]
    simp only [AddCircle.coe_add]
  exact hinv x N hN G hG (by simpa only [heq] using hbad)

end Hindman168
