import Hindman168.IntervalResidueCount
import Hindman168.PrimeResidueLaw
import Hindman168.UnequalDyadicPrimeZeros

/-!
# Elementary residue-atom bounds for actual harmonic prime samples

An interval has at most T/q+1 members in each residue class, regardless
of its location. Multiplying this count by the actual maximum prime atom
gives the large-modulus branch needed in rough coprimality. This is not
the small-modulus Brun--Titchmarsh bound.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def naturalResidueWindow (A T q a : ℕ) : Finset ℕ :=
  (Finset.Ico A (A + T)).filter (fun n => n % q = a)

theorem naturalResidueWindow_cast {A T q a : ℕ} (ha : a < q) :
    (naturalResidueWindow A T q a).map Nat.castEmbedding = intervalResidueSet A T q a := by
  have hN : naturalResidueWindow A T q a =
      (Finset.Ico A (A + T)).filter (fun n => n ≡ a [MOD q]) := by
    ext n
    simp only [naturalResidueWindow, Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt ha]
  have hZ : (Finset.Ico (A : ℤ) ((A + T : ℕ) : ℤ)).filter
      (fun z => z ≡ (a : ℤ) [ZMOD (q : ℤ)]) = intervalResidueSet A T q a := by
    ext z
    simp only [intervalResidueSet, integerWindow, Finset.mem_filter, Int.ModEq, Nat.cast_add,
      Int.emod_eq_of_lt (Int.natCast_nonneg a) (by exact_mod_cast ha : (a : ℤ) < q)]
  rw [hN, Nat.Ico_filter_modEq_cast, hZ]

theorem natural_residue_count {A T q a : ℕ} (hq : 0 < q) (ha : a < q) :
    |((naturalResidueWindow A T q a).card : ℝ) - (T : ℝ) / q| ≤ 1 := by
  have hc := congrArg Finset.card (naturalResidueWindow_cast (A := A) (T := T) ha)
  rw [Finset.card_map] at hc
  rw [hc]
  exact interval_residue_count A T hq ha

theorem natural_residue_count_upper {A T q a : ℕ} (hq : 0 < q) (ha : a < q) :
    ((naturalResidueWindow A T q a).card : ℝ) ≤ (T : ℝ) / q + 1 := by
  have h := (abs_le.mp (natural_residue_count (A := A) (T := T) hq ha)).2
  linarith

theorem primePool_residue_event_bound {A T q a : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A (A + T)) (hq : 0 < q) (ha : a < q) :
    event (primePoolMass A (A + T)) (fun n => n % q = a) ≤
      ((T : ℝ) / q + 1) / ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by
  have hs : (primePoolMass A (A + T)).support ⊆ Finset.Ico A (A + T) := by
    intro n hn
    have hmem := primePool_mem.mp (primePoolMass_support A (A + T) hn)
    exact Finset.mem_Ico.mpr ⟨hmem.1, hmem.2.1⟩
  have hcap : 0 ≤ 1 / ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by positivity
  have he : event (primePoolMass A (A + T)) (fun n => n % q = a) =
      ∑ n ∈ naturalResidueWindow A T q a, primePoolMass A (A + T) n := by
    rw [event_eq_sum _ _ hs]
    simp only [naturalResidueWindow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n % q = a <;> simp only [hn, if_true, if_false]
  rw [he]
  calc
    (∑ n ∈ naturalResidueWindow A T q a, primePoolMass A (A + T) n) ≤
      ∑ _n ∈ naturalResidueWindow A T q a,
        1 / ((A : ℝ) * primePoolHarmonicMass A (A + T)) :=
      Finset.sum_le_sum (fun n _ => primePool_max_atom hA hH n)
    _ = ((naturalResidueWindow A T q a).card : ℝ) *
        (1 / ((A : ℝ) * primePoolHarmonicMass A (A + T))) :=
      by simp
    _ ≤ ((T : ℝ) / q + 1) * (1 / ((A : ℝ) * primePoolHarmonicMass A (A + T))) :=
      mul_le_mul_of_nonneg_right (natural_residue_count_upper hq ha) hcap
    _ = ((T : ℝ) / q + 1) / ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by ring

theorem primePoolResidueMass_eq_event (q A B a : ℕ) :
    primePoolResidueMass q A B a = event (primePoolMass A B) (fun n => n % q = a) := by
  rw [primePoolResidueMass, push_apply, event_eq_sum _ _ (Finset.Subset.refl _)]
  apply Finset.sum_congr rfl
  intro n _
  simp only [eq_comm]

theorem primePoolResidueMass_atom_bound {A T q a : ℕ} (hA : 0 < A)
    (hH : 0 < primePoolHarmonicMass A (A + T)) (hq : 0 < q) (ha : a < q) :
    primePoolResidueMass q A (A + T) a ≤
      ((T : ℝ) / q + 1) / ((A : ℝ) * primePoolHarmonicMass A (A + T)) := by
  rw [primePoolResidueMass_eq_event]
  exact primePool_residue_event_bound hA hH hq ha

theorem dyadicPrimeResidueMass_atom_log_bound {A q a : ℕ} (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hq : 0 < q) (ha : a < q) :
    primePoolResidueMass q A (2 * A) a ≤
      8 * (Real.log (A : ℝ) / A) * ((A : ℝ) / q + 1) := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hlog : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hHpos : 0 < primePoolHarmonicMass A (2 * A) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hlog)).trans_le hH
  have hs : (primePoolMass A (2 * A)).support ⊆ Finset.Ico A (A + A) := by
    intro n hn
    have hm := primePool_mem.mp (primePoolMass_support A (2 * A) hn)
    exact Finset.mem_Ico.mpr ⟨hm.1, by omega⟩
  have hb : 0 ≤ 8 * Real.log (A : ℝ) / A := by positivity
  have he : primePoolResidueMass q A (2 * A) a =
      ∑ n ∈ naturalResidueWindow A A q a, primePoolMass A (2 * A) n := by
    rw [primePoolResidueMass_eq_event, event_eq_sum _ _ hs]
    simp only [naturalResidueWindow, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : n % q = a <;> simp only [hn, if_true, if_false]
  rw [he]
  calc
    (∑ n ∈ naturalResidueWindow A A q a, primePoolMass A (2 * A) n) ≤
      ∑ _n ∈ naturalResidueWindow A A q a,
        8 * Real.log (A : ℝ) / A :=
      Finset.sum_le_sum (fun n _ => primePool_max_atom_log_bound hA hH n)
    _ = ((naturalResidueWindow A A q a).card : ℝ) * (8 * Real.log (A : ℝ) / A) := by simp
    _ ≤ ((A : ℝ) / q + 1) * (8 * Real.log (A : ℝ) / A) :=
      mul_le_mul_of_nonneg_right (natural_residue_count_upper hq ha) hb
    _ = 8 * (Real.log (A : ℝ) / A) * ((A : ℝ) / q + 1) := by ring

theorem dyadicPrimeResidueMass_large_modulus_bound {A q a : ℕ} (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hq : 0 < q) (ha : a < q) (hlarge : Real.sqrt (A : ℝ) ≤ q) :
    primePoolResidueMass q A (2 * A) a ≤ 16 * Real.log (A : ℝ) / Real.sqrt A := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hsqrt : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.mpr hAr
  have hsqsqrt := Real.sq_sqrt hAr.le
  have hlog : 0 ≤ Real.log (A : ℝ) :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < A))).le
  have hsqone : 1 ≤ Real.sqrt (A : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (by exact_mod_cast (by omega : 1 ≤ A) : (1 : ℝ) ≤ A)
  have hquot : (A : ℝ) / q ≤ Real.sqrt A := by
    apply (div_le_iff₀ hqr).mpr
    nlinarith
  have hinv : Real.sqrt (A : ℝ) / A = 1 / Real.sqrt A := by
    apply (div_eq_div_iff hAr.ne' hsqrt.ne').mpr
    simpa only [one_mul, sq] using hsqsqrt
  calc
    _ ≤ 8 * (Real.log (A : ℝ) / A) * ((A : ℝ) / q + 1) :=
      dyadicPrimeResidueMass_atom_log_bound hA hH hq ha
    _ ≤ 8 * (Real.log (A : ℝ) / A) * (2 * Real.sqrt A) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 16 * Real.log (A : ℝ) * (Real.sqrt A / A) := by ring
    _ = _ := by rw [hinv]; ring

theorem dyadicPrimeResidueMass_large_modulus_uniform {L A q a : ℕ}
    (hL : Real.exp 2 ≤ (L : ℝ)) (hLA : L ≤ A) (hA : 2 ≤ A)
    (hH : 1 / (8 * Real.log (A : ℝ)) ≤ primePoolHarmonicMass A (2 * A))
    (hq : 0 < q) (ha : a < q) (hlarge : Real.sqrt (A : ℝ) ≤ q) :
    primePoolResidueMass q A (2 * A) a ≤ 16 * Real.log (L : ℝ) / Real.sqrt L := by
  have hLAr : (L : ℝ) ≤ A := by exact_mod_cast hLA
  have hm := Real.log_div_sqrt_antitoneOn hL (hL.trans hLAr) hLAr
  calc
    _ ≤ 16 * (Real.log (A : ℝ) / Real.sqrt A) := by
      simpa only [mul_div_assoc] using
        dyadicPrimeResidueMass_large_modulus_bound hA hH hq ha hlarge
    _ ≤ 16 * (Real.log (L : ℝ) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

end Hindman168
