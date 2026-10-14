import Hindman168.PolynomialSmallValuesPositive
import Hindman168.FiniteUniformErrorZero

namespace Hindman168
open Polynomial
open scoped Classical

/-- Genuine large-box scalar polynomial small-value inverse, including
constant and zero-tolerance cases. One fixed B precedes the arbitrary real
coefficients, N and epsilon; the original large-N threshold is explicit. -/
theorem polynomial_small_values_inverse (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ B : ℕ, 0 < B ∧ ∀ p : ℝ[X], p.natDegree ≤ D → ∀ N : ℕ, B ≤ N →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ/10 →
        δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε)).card →
        ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ ∀ i : ℕ, i ≤ D →
          (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*ε := by
  obtain ⟨A, T, hA, hT, hpositive⟩ := polynomial_small_values_positive D δ hδ hδ1
  let B := A+T+1
  have hB : 0 < B := by dsimp only [B]; omega
  have hAB : A ≤ B := by dsimp only [B]; omega
  refine ⟨B, hB, ?_⟩
  intro p hp N hBN ε hε hεsmall hdense
  have hTN : T ≤ N := by dsimp only [B] at hBN; omega
  have hN : 0 < N := hT.trans_le hTN
  by_cases hz : ε=0
  · subst ε
    let s := Finset.Icc 1 A
    have hs : s.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hA⟩⟩
    let f := fun q i : ℕ => (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖
    have hsmall : ∀ ε' : ℝ, 0 < ε' → ε' ≤ δ/10 →
        ∃ q ∈ s, ∀ i ∈ Finset.range (D+1), f q i ≤ (A : ℝ)*ε' := by
      intro ε' hε' hε'small
      have hsub : (Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ 0) ⊆
          (Finset.range N).filter (fun n : ℕ =>
            ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε') := by
        intro n hn
        have hv := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hv.1, hv.2.trans hε'.le⟩
      have hd : δ*(N : ℝ) ≤ ((Finset.range N).filter (fun n : ℕ =>
          ‖((p.eval (n : ℝ) : ℝ) : UnitAddCircle)‖ ≤ ε')).card :=
        hdense.trans (by exact_mod_cast Finset.card_le_card hsub)
      obtain ⟨q, hq, hqA, hcoeff⟩ := hpositive p hp N hTN ε' hε' hε'small hd
      exact ⟨q, Finset.mem_Icc.mpr ⟨hq, hqA⟩,
        fun i hi => hcoeff i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))⟩
    obtain ⟨q, hq, hzero⟩ := finite_uniform_error_zero s hs (Finset.range (D+1)) f
      (fun _ _ _ _ => by dsimp only [f]; positivity)
      (δ/10) (A : ℝ) (by positivity) (by exact_mod_cast hA) hsmall
    have hbounds := Finset.mem_Icc.mp hq
    refine ⟨q, hbounds.1, hbounds.2.trans hAB, ?_⟩
    intro i hi
    have he := hzero i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    change (N : ℝ)^i*‖(((q : ℝ)*p.coeff i : ℝ) : UnitAddCircle)‖ = 0 at he
    rw [he, mul_zero]
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hz)
    obtain ⟨q, hq, hqA, hcoeff⟩ := hpositive p hp N hTN ε hεpos hεsmall hdense
    refine ⟨q, hq, hqA.trans hAB, ?_⟩
    intro i hi
    exact (hcoeff i hi).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hAB) hε)

end Hindman168
