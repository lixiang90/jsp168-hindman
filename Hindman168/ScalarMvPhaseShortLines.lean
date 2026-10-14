import Hindman168.ScalarMvLinePolynomial
import Hindman168.ScalarPolynomialSimultaneousInverse
import Hindman168.LeibmanCubeCommonCharacter

namespace Hindman168
open scoped BigOperators Classical

noncomputable def scalarMvPolynomialPhase {κ : Type*}
    (p : MvPolynomial κ ℝ) (x : κ → ℤ) : ℂ :=
  (AddCircle.toCircle ((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle) : ℂ)

theorem scalar_mv_polynomial_phase_norm {κ : Type*}
    (p : MvPolynomial κ ℝ) (x : κ → ℤ) : ‖scalarMvPolynomialPhase p x‖ = 1 :=
  Circle.norm_coe _

theorem scalar_mv_line_phase {κ : Type*}
    (p : MvPolynomial κ ℝ) (x : κ → ℤ) (u : κ → ℕ) (m : ℕ) :
    scalarPolynomialPhase (scalarMvLinePolynomial p (fun j => (x j : ℝ))
      (fun j => (u j : ℝ))) m =
    scalarMvPolynomialPhase p (fun j => x j+(u j : ℤ)*(m : ℤ)) := by
  simp only [scalarPolynomialPhase, scalarMvPolynomialPhase, scalar_mv_line_polynomial_eval,
    Int.cast_add, Int.cast_mul, Int.cast_natCast]

/-- Uniform actual production on every large short line. The candidate
existence input of the retained cube argument is discharged by the PROVED
scalar phase inverse on the actual restricted polynomial. -/
theorem scalar_mv_short_line_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ {κ : Type*} (p : MvPolynomial κ ℝ), p.totalDegree ≤ D →
      ∀ (x : κ → ℤ) (u : κ → ℕ) (H : ℕ), 0 < H →
        δ/2 ≤ ‖finiteComplexSetMean (Finset.range H)
          (fun m => scalarMvPolynomialPhase p (fun j => x j+(u j : ℤ)*(m : ℤ)))‖ →
        ∃ c : ℕ, 0 < c ∧ c ≤ A ∧ ∀ r : ℕ, 0 < r → r ≤ D →
          (H : ℝ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
            (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ A := by
  obtain ⟨A, hA, hinv⟩ := scalar_polynomial_phase_simultaneous_inverse D (δ/2)
    (by positivity) (by linarith)
  refine ⟨A, hA, ?_⟩
  intro κ p hp x u H hH hlarge
  let l := scalarMvLinePolynomial p (fun j => (x j : ℝ)) (fun j => (u j : ℝ))
  have hl : l.natDegree ≤ D := scalar_mv_line_polynomial_degree p _ _ D hp
  have hm : δ/2 ≤ ‖finiteComplexSetMean (Finset.range H) (scalarPolynomialPhase l)‖ := by
    have he : scalarPolynomialPhase l =
        fun m : ℕ => scalarMvPolynomialPhase p (fun j => x j+(u j : ℤ)*(m : ℤ)) :=
      funext (fun m => scalar_mv_line_phase p x u m)
    rw [he]
    exact hlarge
  obtain ⟨c, hc, hcA, hcoeff⟩ := hinv l hl H hH hm
  refine ⟨c, hc, hcA, ?_⟩
  intro r hr hrD
  simpa only [l, scalar_mv_line_polynomial_coefficient] using hcoeff r hr hrD

/-- Genuine common bounded scalar multiplier and dense original basepoints
on many actual directions, with no analytic production hypothesis remaining. -/
theorem scalar_mv_cube_common_line_coefficients {κ : Type*} [Fintype κ]
    (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ p : MvPolynomial κ ℝ, p.totalDegree ≤ D →
      ∀ N L : ℕ, 0 < L → L^2 ≤ N → 8*(Fintype.card κ : ℝ) ≤ δ*L →
        δ ≤ ‖finiteComplexSetMean
          (Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))) (scalarMvPolynomialPhase p)‖ →
        ∃ c : ℕ, 0 < c ∧ c ≤ A ∧
          δ/(8*(A : ℝ))*((Fintype.piFinset (fun _ : κ => Finset.range L)).card : ℝ) ≤
          (((Fintype.piFinset (fun _ : κ => Finset.range L)).filter (fun u =>
            δ/(8*(A : ℝ))*((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).card : ℝ) ≤
              (((Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))).filter (fun x =>
                ∀ r : ℕ, 0 < r → r ≤ D →
                  (N/L^2 : ℕ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
                    (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r) : ℝ) :
                    UnitAddCircle)‖ ≤ (A : ℝ))).card : ℝ))).card : ℝ) := by
  obtain ⟨A, hA, hline⟩ := scalar_mv_short_line_inverse D δ hδ hδ1
  refine ⟨A, hA, ?_⟩
  intro p hp N L hL hN hsize hbad
  let S := Finset.Icc 1 A
  let R := fun c : ℕ => fun u : κ → ℕ => fun x : κ → ℤ =>
    ∀ r : ℕ, 0 < r → r ≤ D →
      (N/L^2 : ℕ)^r*‖(((c : ℝ)*MvPolynomial.eval (fun j => (x j : ℝ))
        (scalarMvLineCoefficient p (fun j => (u j : ℝ)) r) : ℝ) : UnitAddCircle)‖ ≤ (A : ℝ)
  have hH : 0 < N/L^2 := Nat.div_pos hN (by positivity)
  have hproduce : ∀ u ∈ Fintype.piFinset (fun _ : κ => Finset.range L),
      ∀ x ∈ Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ)),
      δ*1/2 ≤ ‖finiteComplexSetMean (Finset.range (N/L^2))
        (fun m => scalarMvPolynomialPhase p (fun j => x j+(u j : ℤ)*(m : ℤ)))‖ →
      ∃ c ∈ S, R c u x := by
    intro u _ x _ hlarge
    obtain ⟨c, hc, hcA, hcoeff⟩ := hline p hp x u (N/L^2) hH (by simpa only [mul_one] using hlarge)
    exact ⟨c, Finset.mem_Icc.mpr ⟨hc, hcA⟩, hcoeff⟩
  obtain ⟨c, hc, hdense⟩ := leibman_equal_cube_common_candidate N L hL hN
    (scalarMvPolynomialPhase p) 1 δ (by positivity) hδ hsize
    (fun x => (scalar_mv_polynomial_phase_norm p x).le)
    (by simpa only [mul_one] using hbad) S R hproduce
  have hcard : S.card = A := by simp only [S, Nat.card_Icc]; omega
  have hb := Finset.mem_Icc.mp hc
  refine ⟨c, hb.1, hb.2, ?_⟩
  simpa only [hcard, R] using hdense

end Hindman168
