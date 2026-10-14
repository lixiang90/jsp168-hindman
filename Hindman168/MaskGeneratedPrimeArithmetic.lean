import Hindman168.MonomialPrimeResidueUnits

/-!
# Arithmetic of the actual mask-generated rows under their master law

The row monomial certificates are derived from the full mask iteration.
Coprimality uses the actual supported pool primes and original local good
condition. Unit estimates apply uniformly to all types and every positive
modulus at most the actual gap auxiliary budget, including the smooth
master modulus. Neither an arithmetic coefficient nor a unit hypothesis
is supplied in these applications.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem maskGenerated_rows_prime_arithmetic (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) (t : Fin (Fintype.card (LargeColumnSubset m)))
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
      ((maskGeneratedMaster m gap).pool w (gap w).val).lower
      ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support)
    (hg : predictionLocalPrimeGoodEvent (maskGeneratedMaster m gap)
      ((maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target)
      ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target)
      w x) :
    ∀ i, (∀ k, (maskGeneratedRowDataFamily m gap t).rows.row i k ≠ 0 →
      0 < (MvPolynomial.eval (fun j => (x j : ℤ))
        ((maskGeneratedRowDataFamily m gap t).rows.row i k)).natAbs) ∧
      ∀ j k, j ≠ k → (maskGeneratedRowDataFamily m gap t).rows.row i j ≠ 0 →
        (maskGeneratedRowDataFamily m gap t).rows.row i k ≠ 0 →
        (MvPolynomial.eval (fun v => (x v : ℤ))
          ((maskGeneratedRowDataFamily m gap t).rows.row i j)).natAbs.Coprime
        (MvPolynomial.eval (fun v => (x v : ℤ))
          ((maskGeneratedRowDataFamily m gap t).rows.row i k)).natAbs := by
  have hp : ∀ j, (x j).Prime := fun j =>
    (primePool_mem.mp (primeIndependentMass_support_pool hx j)).2.2
  intro i
  have hi := maskGeneratedRowDataFamily_monomial m gap t i
  refine ⟨?_, ?_⟩
  · intro k hk
    exact (hi.monomial_of_ne_zero k hk).natAbs_eval_pos x (fun j => (hp j).pos)
  · intro j k hne hj hk
    exact hi.coprime_nonzero_columns j k hne hj hk x hp hg.1.1

theorem maskGenerated_rows_eventually_bounded_units (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support,
      ∀ i k, (maskGeneratedRowDataFamily m gap t).rows.row i k ≠ 0 →
      ∀ a, 0 < a → a ≤ (maskGeneratedMaster m gap).auxiliary w (gap w).val →
        (MvPolynomial.eval (fun j => (x j : ℤ))
          ((maskGeneratedRowDataFamily m gap t).rows.row i k)).natAbs.Coprime a ∧
        IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ))
          ((maskGeneratedRowDataFamily m gap t).rows.row i k) : ℤ) : ZMod a) := by
  apply eventually_all.mpr
  intro t
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have hp := hF.prime_slots_eventually_gt_budget
    (fun w (_ : Fin (maskGeneratedRowDataFamily m gap t).arity) => gap w)
    (fun w => (maskGeneratedMaster m gap).auxiliary w (gap w).val)
    (Eventually.of_forall (fun _ _ => le_rfl))
  filter_upwards [hp] with w hw
  intro x hx i k hk a ha hcap
  have hlarge := hw x hx
  have hmono := (maskGeneratedRowDataFamily_monomial m gap t i).monomial_of_ne_zero k hk
  exact ⟨hmono.natAbs_eval_coprime_bounded x hlarge ha hcap,
    hmono.residue_isUnit_bounded x hlarge ha hcap⟩

theorem maskGenerated_rows_eventually_smooth_units (m : ℕ) {N : ℕ}
    (gap : ℕ → Fin N) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ x ∈ (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
        ((maskGeneratedMaster m gap).pool w (gap w).val).lower
        ((maskGeneratedMaster m gap).pool w (gap w).val).upper).support,
      ∀ i k, (maskGeneratedRowDataFamily m gap t).rows.row i k ≠ 0 →
        IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ))
          ((maskGeneratedRowDataFamily m gap t).rows.row i k) : ℤ) :
          ZMod ((maskGeneratedMaster m gap).modulus w : ℕ)) := by
  filter_upwards [maskGenerated_rows_eventually_bounded_units m gap] with w hw
  intro t x hx i k hk
  exact (hw t x hx i k hk _ ((maskGeneratedMaster m gap).modulus w).pos
    ((maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val)).2

end Hindman168
