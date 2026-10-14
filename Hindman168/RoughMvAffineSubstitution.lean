import Hindman168.RoughVectorMvPolynomial

namespace Hindman168
open MvPolynomial

theorem rough_mv_linear_substitution_degree {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ j, (f j).totalDegree ≤ 1)
    (p : MvPolynomial σ R) : (eval₂Hom C f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => arg 1; rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ j ∈ d.support, (f j ^ d j).totalDegree ≤ ∑ j ∈ d.support, d j := by
      apply Finset.sum_le_sum
      intro j _
      exact (totalDegree_pow _ _).trans
        (by simpa only [mul_one] using Nat.mul_le_mul_left (d j) (hf j))
    _ ≤ p.totalDegree := le_totalDegree hd

noncomputable def roughMvAffineSubstitution {σ R : Type*} [CommSemiring R]
    (u k : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun j => C (u j) + C (k j) * X j)

theorem roughMvAffineSubstitution_degree {σ R : Type*} [CommSemiring R]
    (u k : σ → R) (p : MvPolynomial σ R) :
    (roughMvAffineSubstitution u k p).totalDegree ≤ p.totalDegree := by
  apply rough_mv_linear_substitution_degree
  intro j
  apply (totalDegree_add _ _).trans
  apply max_le (by simp only [totalDegree_C]; exact Nat.zero_le _)
  exact (totalDegree_mul _ _).trans
    (by simpa only [totalDegree_C, zero_add, X, Finsupp.sum_single_index, id_eq] using
      (totalDegree_monomial_le (Finsupp.single j 1) (1 : R)))

theorem roughMvAffineSubstitution_eval {σ R : Type*} [CommSemiring R]
    (u k x : σ → R) (p : MvPolynomial σ R) :
    eval x (roughMvAffineSubstitution u k p) = eval (fun j => u j + k j * x j) p := by
  change eval x (eval₂ C _ p) = _
  rw [← eval_assoc]
  apply congrArg (fun v : σ → R => eval v p)
  funext j
  simp only [Function.comp_apply, map_add, map_mul, eval_C, eval_X]

noncomputable def roughVectorMvAffineSubstitution {σ E : Type*}
    (u k : σ → ℝ) (p : RoughVectorMvPolynomial σ E) : RoughVectorMvPolynomial σ E :=
  p.map (fun a => (roughMvAffineSubstitution u k a.1, a.2))

theorem roughVectorMvAffineSubstitution_degree {σ E : Type*}
    (u k : σ → ℝ) {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughVectorMvAffineSubstitution u k p) d := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (roughMvAffineSubstitution_degree u k b.1).trans (hp b hb)

theorem roughVectorMvAffineSubstitution_eval {σ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u k x : σ → ℝ) (p : RoughVectorMvPolynomial σ E) :
    roughVectorMvEval (roughVectorMvAffineSubstitution u k p) x =
      roughVectorMvEval p (fun j => u j + k j * x j) := by
  unfold roughVectorMvAffineSubstitution roughVectorMvEval
  simp only [List.map_map, Function.comp_def, roughMvAffineSubstitution_eval]

end Hindman168
