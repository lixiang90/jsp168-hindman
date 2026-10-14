import Hindman168.SquarefreeHarmonicLower

/-!
# Uniform squarefree harmonic lower bounds with one prime omitted

Squarefree integers divisible by q map injectively, by division by q,
to squarefree integers not divisible by q. Their reciprocal weights only
increase under this map. Thus omitting any prime loses at most a factor
two, independently of that prime or the cutoff.
-/

namespace Hindman168

open scoped BigOperators Classical

def primeOmittedSquarefreeWindow (q z : ℕ) : Finset ℕ :=
  (squarefreeWindow z).filter (fun d => ¬ q ∣ d)

noncomputable def primeOmittedHarmonic (q z : ℕ) : ℝ :=
  ∑ d ∈ primeOmittedSquarefreeWindow q z, (d : ℝ)⁻¹

theorem primeOmittedHarmonic_nonneg (q z : ℕ) : 0 ≤ primeOmittedHarmonic q z :=
  Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))

theorem squarefree_prime_quotient_mem {q z n : ℕ} (hq : q.Prime)
    (hn : n ∈ squarefreeWindow z) (hqn : q ∣ n) :
    n / q ∈ primeOmittedSquarefreeWindow q z := by
  obtain ⟨hni, hsf⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnpos, hnz⟩ := Finset.mem_Icc.mp hni
  have hqle : q ≤ n := Nat.le_of_dvd hnpos hqn
  have htpos : 0 < n / q := Nat.div_pos hqle hq.pos
  have htn : n / q ∣ n := Nat.div_dvd_of_dvd hqn
  have hnot : ¬ q ∣ n / q := by
    intro h
    apply hq.not_isUnit
    exact hsf q ((Nat.dvd_div_iff_mul_dvd hqn).mp h)
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨htpos, (Nat.div_le_self n q).trans hnz⟩,
      hsf.squarefree_of_dvd htn⟩, hnot⟩

theorem prime_quotient_injOn_multiples (q : ℕ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, q ∣ n) : Set.InjOn (fun n : ℕ => n / q) (S : Set ℕ) := by
  intro n hn m hm he
  calc
    n = n / q * q := (Nat.div_mul_cancel (hS n hn)).symm
    _ = m / q * q := congrArg (fun k => k * q) he
    _ = m := Nat.div_mul_cancel (hS m hm)

theorem squarefreeHarmonic_le_twice_primeOmitted {q : ℕ} (hq : q.Prime) (z : ℕ) :
    squarefreeHarmonic z ≤ 2 * primeOmittedHarmonic q z := by
  let B := (squarefreeWindow z).filter (fun n => q ∣ n)
  have hB : ∀ n ∈ B, q ∣ n := fun n hn => (Finset.mem_filter.mp hn).2
  have hi := prime_quotient_injOn_multiples q B hB
  have hs : B.image (fun n => n / q) ⊆ primeOmittedSquarefreeWindow q z := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact squarefree_prime_quotient_mem hq (Finset.mem_filter.mp hn).1 (hB n hn)
  have hbad : (∑ n ∈ B, (n : ℝ)⁻¹) ≤ primeOmittedHarmonic q z := by
    calc
      _ ≤ ∑ n ∈ B, ((n / q : ℕ) : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro n hn
        have hm := squarefree_prime_quotient_mem hq (Finset.mem_filter.mp hn).1 (hB n hn)
        have htpos : 0 < n / q :=
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
        have htr : (0 : ℝ) < (n / q : ℕ) := by exact_mod_cast htpos
        simpa only [one_div] using one_div_le_one_div_of_le htr
          (by exact_mod_cast Nat.div_le_self n q)
      _ = ∑ t ∈ B.image (fun n => n / q), (t : ℝ)⁻¹ := by rw [Finset.sum_image hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => by positivity)
  have he : squarefreeHarmonic z = primeOmittedHarmonic q z + ∑ n ∈ B, (n : ℝ)⁻¹ := by
    simp only [squarefreeHarmonic, primeOmittedHarmonic, primeOmittedSquarefreeWindow,
      B, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : q ∣ n <;> simp only [hn, not_true_eq_false, not_false_eq_true, if_true,
      if_false, zero_add, add_zero]
  rw [he]
  linarith

theorem primeOmittedHarmonic_log_lower {q : ℕ} (hq : q.Prime) (z : ℕ) :
    Real.log (z + 1 : ℕ) / 4 ≤ primeOmittedHarmonic q z := by
  have hs := squarefreeHarmonic_log_lower z
  have hqz := squarefreeHarmonic_le_twice_primeOmitted hq z
  linarith

end Hindman168
