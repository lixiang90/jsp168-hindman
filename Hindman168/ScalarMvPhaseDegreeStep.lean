import Hindman168.ScalarMvCommonHomogeneousDirections
import Hindman168.ScalarMvShortLineThreshold
import Hindman168.LeibmanSimultaneousDirectionReconstruction

namespace Hindman168
open scoped BigOperators Classical

/-- Genuine scalar multiparameter phase degree STEP. Only the lower-degree
small-value induction hypothesis remains explicit. All short-line production,
common candidates, original thresholds and coefficient reconstruction are proved. -/
theorem scalar_mv_phase_degree_step (n D : ℕ)
    (hsmall : ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      ∃ B : ℕ, 0 < B ∧ ScalarMvSmallValueEstimate (Fin n) D μ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ D+1 →
      ∀ N : ℕ, 0 < N → δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
        (scalarMvPolynomialPhase p)‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ K ∧ ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
          (N : ℝ)^(∑ j, J j)*‖(((Q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ (K : ℝ) := by
  obtain ⟨A, hA, hcube⟩ := scalar_mv_cube_common_line_coefficients (κ := Fin n) (D+1) δ hδ hδ1
  let μ := δ/(8*(A : ℝ))
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hμ1 : μ ≤ 1 := by
    dsimp only [μ]
    apply (div_le_one₀ (by positivity : (0 : ℝ) < 8*(A : ℝ))).mpr
    have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
    linarith only [hAr, hδ1]
  obtain ⟨B, hB, hsmallB⟩ := hsmall μ hμ hμ1
  let P := B^(D+2)
  have hP : 0 < P := by dsimp only [P]; positivity
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  obtain ⟨L, hLbound⟩ := exists_nat_gt (max (8*(n : ℝ)/δ) (((D+1 : ℕ)*(P : ℝ))/μ)+1)
  have hmax : max (8*(n : ℝ)/δ) (((D+1 : ℕ)*(P : ℝ))/μ) < L :=
    lt_of_le_of_lt (le_add_of_nonneg_right zero_le_one) hLbound
  have hLleft : 8*(n : ℝ)/δ < L := lt_of_le_of_lt (le_max_left _ _) hmax
  have hLright : ((D+1 : ℕ)*(P : ℝ))/μ < L := lt_of_le_of_lt (le_max_right _ _) hmax
  have hLr : (0 : ℝ) < L := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 8*(n : ℝ)/δ) hLleft
  have hL : 0 < L := by exact_mod_cast hLr
  have hsize : 8*(Fintype.card (Fin n) : ℝ) ≤ δ*L := by
    have h := (div_lt_iff₀ hδ).mp hLleft
    simpa only [Fintype.card_fin, mul_comm] using h.le
  have hdir : (D+1 : ℕ) < (μ/(P : ℝ))*(L : ℝ) := by
    have h := (div_lt_iff₀ hμ).mp hLright
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hPr).mpr
    simpa only [mul_comm] using h
  have hpi : @Fintype.piFinset (Fin n) (Classical.decEq _) (Fin.fintype n)
      (fun _ => ℕ) (fun _ => Finset.range L) =
      Fintype.piFinset (fun _ : Fin n => Finset.range L) := by
    ext u
    simp only [Fintype.mem_piFinset]
  let I := fun r : Fin (D+1) => scalarMvHomogeneousIndices (Fin n) (r.val+1)
  have hI : ∀ r, ∀ J ∈ I r, (∑ j, J j) ≤ D+1 := by
    intro r J hJ
    have he := (scalar_mv_homogeneous_indices_mem (r.val+1) J).mp hJ
    omega
  obtain ⟨C, hC, hreconstruct⟩ := leibman_simultaneous_direction_coefficient_bound I (D+1) hI L hL
  obtain ⟨T₀, hT₀, hthreshold⟩ := scalar_mv_short_line_threshold L B A hL μ hμ
  let K := C*P*A*(2*L^2)^(D+1)+C*P*A+T₀^(D+1)+1
  have hK : 0 < K := by dsimp only [K]; omega
  have hCK : C*P*A*(2*L^2)^(D+1) ≤ K := by dsimp only [K]; omega
  have hQK : C*P*A ≤ K := by dsimp only [K]; omega
  have hTK : T₀^(D+1) ≤ K := by dsimp only [K]; omega
  refine ⟨K, hK, ?_⟩
  intro p hp N hN hbad
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hTN : T₀ ≤ N
  · obtain ⟨hBN, hLN, hH, htol, hscale⟩ := hthreshold N hTN
    let H := N/L^2
    obtain ⟨c, hc, hcA, hdense⟩ := hcube p hp N L hL hLN hsize hbad
    let s := (Fintype.piFinset (fun _ : Fin n => Finset.range L)).filter (fun u =>
      μ*((scalarMvIntegerCube (Fin n) N).card : ℝ) ≤
        ((scalarMvIntegerCube (Fin n) N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ D+1 →
          (H : ℝ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
            (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ A)).card)
    have hs : s ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) := Finset.filter_subset _ _
    have hcount : μ*(L : ℝ)^(Fintype.card (Fin n)) ≤ s.card := by
      simpa only [hpi, s, μ, H, scalarMvIntegerCube, Fintype.card_piFinset,
        Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow] using hdense
    obtain ⟨m, hm, hmP, U, hU, hUdense, hUcoeff⟩ := scalar_mv_common_homogeneous_directions
      D B hB μ hsmallB p hp N H L c hBN hH (A : ℝ) (Nat.cast_nonneg A) htol s
      (by simpa only [hpi] using hs) hcount
      (fun u hu => (Finset.mem_filter.mp hu).2)
    have hspan : (D+1)*L^n < U.card*L :=
      leibman_direction_density_card_condition (D+1) L hL U (μ/(P : ℝ)) hdir
        (by simpa only [P, Fintype.card_fin] using hUdense)
    obtain ⟨k, hk, hkC, hcoeff⟩ := hreconstruct U (by simpa only [hpi] using hU) hspan
    let Q := k*m*c
    have hQ : 0 < Q := by dsimp only [Q]; positivity
    have hQC : Q ≤ C*P*A := by
      dsimp only [Q]
      exact Nat.mul_le_mul (Nat.mul_le_mul hkC hmP) hcA
    refine ⟨Q, hQ, hQC.trans hQK, ?_⟩
    intro J hJ
    by_cases hJD : (∑ j, J j) ≤ D+1
    · let r : Fin (D+1) := ⟨(∑ j, J j)-1, by omega⟩
      have hr : r.val+1=(∑ j, J j) := by dsimp only [r]; omega
      have hJI : J ∈ I r := (scalar_mv_homogeneous_indices_mem _ _).mpr hr.symm
      let a := fun W : ↥(I r) => (m : ℝ)*((c : ℝ)*
        MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm W.val) p)
      have hvalues : ∀ u : ↥U, ‖((∑ W : ↥(I r), a W*
          leibmanMonomialVector (I r) (fun j => (u.val j : ℝ)) W : ℝ) : UnitAddCircle)‖ ≤
          (P : ℝ)*((A : ℝ)/(H : ℝ)^(r.val+1)) := by
        intro u
        have he : (∑ W : ↥(I r), a W*leibmanMonomialVector (I r) (fun j => (u.val j : ℝ)) W) =
            (m : ℝ)*((c : ℝ)*MvPolynomial.coeff 0
              (scalarMvLineCoefficient p (fun j => (u.val j : ℝ)) (r.val+1))) := by
          rw [scalar_mv_line_constant_monomial_vector]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro W _
          dsimp only [a, I]
          ring
        rw [he]
        exact hUcoeff u.val u.property (r.val+1) (by omega) (by omega)
      have he := hcoeff r a ((P : ℝ)*((A : ℝ)/(H : ℝ)^(r.val+1))) (by positivity) hvalues ⟨J, hJI⟩
      have hnorm : ‖(((Q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p : ℝ) :
          UnitAddCircle)‖ ≤ (C : ℝ)*((P : ℝ)*((A : ℝ)/(H : ℝ)^(∑ j, J j))) := by
        have hqeq : (Q : ℝ)*MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p =
            (k : ℝ)*a ⟨J, hJI⟩ := by dsimp only [Q, a]; push_cast; ring
        rw [hqeq]
        simpa only [hr] using he
      have hHr : (0 : ℝ) < H := by exact_mod_cast hH
      have hNH : (N : ℝ) ≤ ((2*L^2 : ℕ) : ℝ)*(H : ℝ) := by exact_mod_cast hscale
      have hbase : (1 : ℝ) ≤ (2*L^2 : ℕ) := by
        have hp : 0 < 2*L^2 := by positivity
        exact_mod_cast hp
      have hpow : (N : ℝ)^(∑ j, J j)/(H : ℝ)^(∑ j, J j) ≤ ((2*L^2 : ℕ) : ℝ)^(D+1) := by
        apply le_trans _ (pow_le_pow_right₀ hbase hJD)
        apply (div_le_iff₀ (pow_pos hHr _)).mpr
        rw [← mul_pow]
        exact pow_le_pow_left₀ hNr.le hNH _
      calc
        _ ≤ (N : ℝ)^(∑ j, J j)*((C : ℝ)*((P : ℝ)*((A : ℝ)/(H : ℝ)^(∑ j, J j)))) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
        _ = ((C : ℝ)*(P : ℝ)*(A : ℝ))*((N : ℝ)^(∑ j, J j)/(H : ℝ)^(∑ j, J j)) := by ring
        _ ≤ ((C : ℝ)*(P : ℝ)*(A : ℝ))*((2*L^2 : ℕ) : ℝ)^(D+1) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (C*P*A*(2*L^2)^(D+1) : ℕ) := by push_cast; ring
        _ ≤ _ := by exact_mod_cast hCK
    · rw [scalar_mv_coefficient_zero_above_degree p (D+1) hp J (Nat.lt_of_not_ge hJD),
        mul_zero, AddCircle.coe_zero, norm_zero, mul_zero]
      positivity
  · refine ⟨1, by omega, hK, ?_⟩
    intro J hJ
    by_cases hJD : (∑ j, J j) ≤ D+1
    · have hNT : (N : ℝ) ≤ T₀ := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hTN))
      have hpw : (N : ℝ)^(∑ j, J j) ≤ (T₀ : ℝ)^(D+1) :=
        (pow_le_pow_left₀ hNr.le hNT _).trans (pow_le_pow_right₀ (by exact_mod_cast hT₀) hJD)
      have hnorm : ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ 1 := by
        have h := AddCircle.norm_le_half_period (1 : ℝ)
          (x := ((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)) (by norm_num)
        norm_num at h
        linarith only [h]
      simp only [Nat.cast_one, one_mul]
      have hb : (N : ℝ)^(∑ j, J j)*‖((MvPolynomial.coeff
          (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ (N : ℝ)^(∑ j, J j) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm (pow_nonneg hNr.le _)
      exact hb.trans (hpw.trans (by exact_mod_cast hTK))
    · rw [scalar_mv_coefficient_zero_above_degree p (D+1) hp J (Nat.lt_of_not_ge hJD),
        mul_zero, AddCircle.coe_zero, norm_zero, mul_zero]
      positivity

/-- The degree-one multiparameter phase inverse is unconditional: the
small-value base supplied to the degree step is already genuinely proved. -/
theorem scalar_mv_linear_phase_inverse (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : ℕ, 0 < K ∧ ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 1 →
      ∀ N : ℕ, 0 < N → δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube (Fin n) N)
        (scalarMvPolynomialPhase p)‖ →
        ∃ Q : ℕ, 0 < Q ∧ Q ≤ K ∧ ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
          (N : ℝ)^(∑ j, J j)*‖(((Q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm J) p : ℝ) : UnitAddCircle)‖ ≤ (K : ℝ) := by
  exact scalar_mv_phase_degree_step n 0
    (fun μ hμ _ => ⟨1, by omega, scalar_mv_small_value_estimate_zero (Fin n) μ hμ⟩) δ hδ hδ1

end Hindman168
