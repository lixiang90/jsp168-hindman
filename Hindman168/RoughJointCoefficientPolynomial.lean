import Hindman168.RoughSpatialSubstitution
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace Hindman168
open MvPolynomial

noncomputable def roughProgressionPolynomial {κ R : Type*} [CommSemiring R]
    (P : Polynomial R) : MvPolynomial (Option κ) R :=
  Polynomial.eval₂ C (X none) P

theorem roughProgressionPolynomial_degree {κ R : Type*} [CommSemiring R]
    (P : Polynomial R) :
    (roughProgressionPolynomial (κ := κ) P).totalDegree ≤ P.natDegree := by
  classical
  unfold roughProgressionPolynomial
  rw [Polynomial.eval₂_eq_sum_range]
  apply totalDegree_finsetSum_le
  intro n hn
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  have hx : (X (none : Option κ) : MvPolynomial (Option κ) R).totalDegree ≤ 1 := by
    simpa only [X, Finsupp.sum_single_index, id_eq] using
      (totalDegree_monomial_le (Finsupp.single none 1) (1 : R))
  have hn' : n * (X (none : Option κ) : MvPolynomial (Option κ) R).totalDegree ≤ n := by
    simpa only [mul_one] using Nat.mul_le_mul_left n hx
  exact (totalDegree_pow _ _).trans
    (hn'.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))

theorem roughProgressionPolynomial_eval {κ R : Type*} [CommSemiring R]
    (P : Polynomial R) (z : R) (x : κ → R) :
    eval (Option.elim · z x) (roughProgressionPolynomial P) = P.eval z := by
  classical
  unfold roughProgressionPolynomial
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
  simp only [map_sum, map_mul, eval_C, map_pow, eval_X, Option.elim_none]

noncomputable def roughSpatialFixedPolynomial {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (a0 : R) (a : (κ →₀ ℕ) → R) : MvPolynomial κ R :=
  C a0 + ∑ I ∈ s, monomial I (a I)

noncomputable def roughSpatialJointPolynomial {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (M0 : Polynomial R) (M : (κ →₀ ℕ) → Polynomial R) :
    MvPolynomial (Option κ) R :=
  roughProgressionPolynomial M0 +
    ∑ I ∈ s, roughProgressionPolynomial (M I) * rename Option.some (monomial I 1)

theorem roughSpatialJointPolynomial_degree {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (M0 : Polynomial R) (M : (κ →₀ ℕ) → Polynomial R)
    (q : ℕ) (h0 : M0.natDegree ≤ q)
    (hM : ∀ I ∈ s, (M I).natDegree + I.sum (fun _ e => e) ≤ q) :
    (roughSpatialJointPolynomial s M0 M).totalDegree ≤ q := by
  unfold roughSpatialJointPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le ((roughProgressionPolynomial_degree M0).trans h0)
  apply totalDegree_finsetSum_le
  intro I hI
  exact (totalDegree_mul _ _).trans ((Nat.add_le_add
    (roughProgressionPolynomial_degree (M I))
    ((totalDegree_rename_le Option.some _).trans (totalDegree_monomial_le I 1))).trans (hM I hI))

theorem roughSpatialJointPolynomial_eval {κ R : Type*} [CommSemiring R]
    (s : Finset (κ →₀ ℕ)) (M0 : Polynomial R) (M : (κ →₀ ℕ) → Polynomial R)
    (z : R) (x : κ → R) :
    eval (Option.elim · z x) (roughSpatialJointPolynomial s M0 M) =
      eval x (roughSpatialFixedPolynomial s (M0.eval z) (fun I => (M I).eval z)) := by
  classical
  simp only [roughSpatialJointPolynomial, roughSpatialFixedPolynomial,
    map_add, map_sum, map_mul, roughProgressionPolynomial_eval, eval_C, eval_rename,
    eval_monomial, one_mul]
  rfl

end Hindman168
