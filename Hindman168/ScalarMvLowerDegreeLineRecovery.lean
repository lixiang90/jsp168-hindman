import Hindman168.ScalarMvIntegerCube
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open scoped BigOperators Classical

/-- The actual lower-degree step needed for degree induction. The only
inverse hypothesis is the intended small-value induction hypothesis at
degree D, on the ORIGINAL integer cube. Every line polynomial, coefficient,
degree bound, dense sample inclusion and common multiplier is proved here. -/
theorem scalar_mv_lower_degree_line_recovery {κ : Type*} [Fintype κ]
    (D B : ℕ) (hB : 0 < B) (μ : ℝ)
    (hsmall : ∀ f : MvPolynomial κ ℝ, f.totalDegree ≤ D →
      ∀ N : ℕ, B ≤ N → ∀ ε : ℝ, 0 ≤ ε → ε ≤ μ/10 →
        μ*((scalarMvIntegerCube κ N).card : ℝ) ≤
          ((scalarMvIntegerCube κ N).filter (fun x =>
            ‖((MvPolynomial.eval (fun j => (x j : ℝ)) f : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ I : κ → ℕ,
          (N : ℝ)^(∑ j, I j)*‖(((q : ℝ)*MvPolynomial.coeff
            (Finsupp.equivFunOnFinite.symm I) f : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε)
    (p : MvPolynomial κ ℝ) (hp : p.totalDegree ≤ D+1) (u : κ → ℝ)
    (N H c : ℕ) (hBN : B ≤ N) (hH : 0 < H) (A : ℝ) (hA : 0 ≤ A)
    (hεsmall : A/(H : ℝ) ≤ μ/10)
    (hdense : μ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ D+1 →
        (H : ℝ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
          (scalarMvLineCoefficient p u r) : ℝ) : UnitAddCircle)‖ ≤ A)).card) :
    ∃ M : ℕ, 0 < M ∧ M ≤ B^(D+2) ∧ ∀ r : ℕ, 0 < r → r ≤ D+1 →
      ‖(((M : ℝ)*((c : ℝ)*MvPolynomial.coeff 0 (scalarMvLineCoefficient p u r)) : ℝ) :
        UnitAddCircle)‖ ≤ (B^(D+2) : ℕ)*(A/(H : ℝ)^r) := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by positivity
  have hdata : ∀ i : Fin (D+1), ∃ q : ℕ, 0 < q ∧ q ≤ B ∧
      ‖(((q : ℝ)*((c : ℝ)*MvPolynomial.coeff 0
        (scalarMvLineCoefficient p u (i.val+1))) : ℝ) : UnitAddCircle)‖ ≤
          (B : ℝ)*(A/(H : ℝ)^(i.val+1)) := by
    intro i
    let r := i.val+1
    have hr : 0 < r := by dsimp only [r]; omega
    have hrD : r ≤ D+1 := by dsimp only [r]; omega
    let f := scalarMvLineCoefficient (MvPolynomial.C (c : ℝ)*p) u r
    have hf : f.totalDegree ≤ D := by
      rw [show f = MvPolynomial.C (c : ℝ)*scalarMvLineCoefficient p u r from
        scalar_mv_line_coefficient_scale p u r (c : ℝ)]
      apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact (scalar_mv_line_coefficient_degree p u (D+1) r hp).trans (by omega)
    have heval (x : κ → ℤ) : MvPolynomial.eval (fun j => (x j : ℝ)) f =
        (c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ)) (scalarMvLineCoefficient p u r) := by
      dsimp only [f]
      rw [scalar_mv_line_coefficient_scale, map_mul, MvPolynomial.eval_C]
    have htol : A/(H : ℝ)^r ≤ μ/10 := by
      have hpow : (H : ℝ) ≤ (H : ℝ)^r := by
        simpa only [pow_one] using pow_le_pow_right₀ hHr hr
      exact (div_le_div_of_nonneg_left hA hHpos hpow).trans hεsmall
    have hsub : ((scalarMvIntegerCube κ N).filter (fun x => ∀ r : ℕ, 0 < r → r ≤ D+1 →
        (H : ℝ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
          (scalarMvLineCoefficient p u r) : ℝ) : UnitAddCircle)‖ ≤ A)) ⊆
        (scalarMvIntegerCube κ N).filter (fun x =>
          ‖((MvPolynomial.eval (fun j => (x j : ℝ)) f : ℝ) : UnitAddCircle)‖ ≤ A/(H : ℝ)^r) := by
      intro x hx
      obtain ⟨hxS, hxcoeff⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hxS, ?_⟩
      rw [heval, le_div_iff₀ (pow_pos hHpos r)]
      simpa only [mul_comm] using hxcoeff r hr hrD
    have hd : μ*((scalarMvIntegerCube κ N).card : ℝ) ≤
        ((scalarMvIntegerCube κ N).filter (fun x =>
          ‖((MvPolynomial.eval (fun j => (x j : ℝ)) f : ℝ) : UnitAddCircle)‖ ≤ A/(H : ℝ)^r)).card :=
      hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
    obtain ⟨q, hq, hqB, hcoeff⟩ := hsmall f hf N hBN (A/(H : ℝ)^r) (by positivity) htol hd
    have hc := hcoeff (fun _ => 0)
    have hz : Finsupp.equivFunOnFinite.symm (fun _ : κ => 0) = (0 : κ →₀ ℕ) := by
      ext j
      simp only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply]
    simp only [hz, Finset.sum_const_zero, pow_zero, one_mul] at hc
    dsimp only [f] at hc
    rw [scalar_mv_line_coefficient_scale, MvPolynomial.coeff_C_mul] at hc
    exact ⟨q, hq, hqB, hc⟩
  choose q hq hqB hcoeff using hdata
  obtain ⟨M, hM, hMB, hmult⟩ := finite_mod_one_common_multiplier q B hB hq hqB
  refine ⟨M, hM, by simpa only [Fintype.card_fin, Nat.add_assoc] using hMB, ?_⟩
  intro r hr hrD
  let i : Fin (D+1) := ⟨r-1, by omega⟩
  have hir : i.val+1=r := by dsimp only [i]; omega
  have h := hmult i ((c : ℝ)*MvPolynomial.coeff 0 (scalarMvLineCoefficient p u r))
    (A/(H : ℝ)^r) (by positivity) (by simpa only [hir] using hcoeff i)
  simpa only [Fintype.card_fin, Nat.add_assoc] using h

end Hindman168
