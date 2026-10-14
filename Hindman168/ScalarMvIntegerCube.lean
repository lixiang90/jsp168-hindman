import Hindman168.ScalarMvHomogeneousIndices
import Hindman168.ScalarMvPhaseShortLines

namespace Hindman168
open scoped BigOperators Classical

noncomputable def scalarMvIntegerCube (κ : Type*) [Fintype κ] (N : ℕ) : Finset (κ → ℤ) :=
  Fintype.piFinset (fun _ : κ => Finset.Ico 0 (N : ℤ))

theorem scalar_mv_integer_cube_card (κ : Type*) [Fintype κ] (N : ℕ) :
    (scalarMvIntegerCube κ N).card = N^(Fintype.card κ) := by
  rw [scalarMvIntegerCube, Fintype.card_piFinset]
  simp only [Int.card_Ico, sub_zero, Int.toNat_natCast, Finset.prod_const, Finset.card_univ]

theorem scalar_mv_integer_cube_nonempty (κ : Type*) [Fintype κ] (N : ℕ) (hN : 0 < N) :
    (scalarMvIntegerCube κ N).Nonempty := by
  apply Fintype.piFinset_nonempty.mpr
  intro j
  exact ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast hN⟩⟩

theorem scalar_mv_integer_cube_dense_sample {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (N : ℕ) (hN : 0 < N) (δ ε : ℝ) (hδ : 0 < δ)
    (hdense : δ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x =>
        ‖((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    ∃ x ∈ scalarMvIntegerCube κ N,
      ‖((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤ ε := by
  have hs : (0 : ℝ) < (scalarMvIntegerCube κ N).card := by
    exact_mod_cast Finset.card_pos.mpr (scalar_mv_integer_cube_nonempty κ N hN)
  have hf : 0 < ((scalarMvIntegerCube κ N).filter (fun x =>
      ‖((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤ ε)).card := by
    have hp := (mul_pos hδ hs).trans_le hdense
    exact_mod_cast hp
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hf
  exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- Actual small-value base of the multivariable degree induction,
including constant and zero tolerance on the ORIGINAL nonempty cube. -/
theorem scalar_mv_small_values_degree_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (hp : p.totalDegree = 0) (N : ℕ) (hN : 0 < N)
    (δ ε : ℝ) (hδ : 0 < δ)
    (hdense : δ*((scalarMvIntegerCube κ N).card : ℝ) ≤
      ((scalarMvIntegerCube κ N).filter (fun x =>
        ‖((MvPolynomial.eval (fun j => (x j : ℝ)) p : ℝ) : UnitAddCircle)‖ ≤ ε)).card) :
    ∀ I : κ → ℕ,
      (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) :
        UnitAddCircle)‖ ≤ ε := by
  obtain ⟨x, _, hx⟩ := scalar_mv_integer_cube_dense_sample p N hN δ ε hδ hdense
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp
  have hconstant : ‖((MvPolynomial.coeff 0 p : ℝ) : UnitAddCircle)‖ ≤ ε := by
    have he : MvPolynomial.eval (fun j => (x j : ℝ)) p = MvPolynomial.coeff 0 p := by
      calc
        _ = MvPolynomial.eval (fun j => (x j : ℝ)) (MvPolynomial.C (MvPolynomial.coeff 0 p)) :=
          congrArg (MvPolynomial.eval (fun j => (x j : ℝ))) hc
        _ = _ := MvPolynomial.eval_C _
    rw [he] at hx
    exact hx
  have hε : 0 ≤ ε := (norm_nonneg _).trans hconstant
  intro I
  by_cases hz : (∑ j, I j)=0
  · have hi : ∀ j, I j=0 := fun j => by
      have hh := Finset.single_le_sum (fun k _ => Nat.zero_le (I k)) (Finset.mem_univ j)
      omega
    have hI : Finsupp.equivFunOnFinite.symm I = 0 := by
      ext j
      simpa only [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_zero, Pi.zero_apply] using hi j
    simpa only [hz, pow_zero, hI, one_mul] using hconstant
  · have hzero := scalar_mv_coefficient_zero_above_degree p 0 hp.le I (by omega)
    simp only [hzero, AddCircle.coe_zero, norm_zero, mul_zero]
    exact hε

theorem scalar_mv_phase_degree_zero {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (hp : p.totalDegree = 0) (N : ℕ) :
    ∀ I : κ → ℕ, 0 < (∑ j, I j) →
      (N : ℝ)^(∑ j, I j)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) :
        UnitAddCircle)‖ = 0 := by
  intro I hI
  rw [scalar_mv_coefficient_zero_above_degree p 0 hp.le I hI,
    AddCircle.coe_zero, norm_zero, mul_zero]

end Hindman168
