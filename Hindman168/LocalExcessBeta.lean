import Hindman168.TopRowValuations
import Hindman168.IndependentRowMinors

/-!
# The paper's actual nonnegative local excess majorant

Beta is zero when at most one row valuation is positive. Otherwise its
exponent removes the largest valuation on the polynomial-test event and
the actual largest distinct pair sum off that event. The primitive and
independent-row bounds give 0 <= alpha-1 <= beta for the original local
kernel count. Beta itself is nonnegative and bounded independently of
the row coefficients and of the polynomial-test event.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def localExcessBeta {q : ℕ} (p : ℕ) (a : Fin q → ℕ) (bad : Prop) : ℝ := by
  classical
  exact if (positiveRowSet a).card ≤ 1 then 0 else
    if bad then ((p ^ ((∑ u, a u) - rowMaxValuation a) : ℕ) : ℝ) - 1
    else ((p ^ ((∑ u, a u) - rowTopTwoSum a) : ℕ) : ℝ) - 1

theorem primePowerLocalAlpha_few_positive (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (hfew : (positiveRowSet a).card ≤ 1)
    (hprimitive : ∀ u, ∃ j, (c u j : ZMod p) ≠ 0) :
    primePowerLocalAlpha p q d A a ha c = 1 := by
  by_cases hz : ∀ u, a u = 0
  · exact primePowerLocalAlpha_all_zero p q d A a ha c hz
  · obtain ⟨u, hu⟩ := not_forall.mp hz
    have hup : 0 < a u := by omega
    have hother (v : Fin q) (hvu : v ≠ u) : a v = 0 := by
      by_contra hv
      have hvp : 0 < a v := by omega
      exact hvu (Finset.card_le_one.mp hfew v ((mem_positiveRowSet a v).mpr hvp)
        u ((mem_positiveRowSet a u).mpr hup))
    exact primePowerLocalAlpha_single_positive p q d A hp a ha c u hother (hprimitive u)

theorem localExcessBeta_eq_zero_of_few {p q : ℕ} (a : Fin q → ℕ) (bad : Prop)
    (h : (positiveRowSet a).card ≤ 1) : localExcessBeta p a bad = 0 := by
  simp only [localExcessBeta, if_pos h]

theorem localExcessBeta_nonneg (p : ℕ) [NeZero p] {q : ℕ} (a : Fin q → ℕ) (bad : Prop) :
    0 ≤ localExcessBeta p a bad := by
  have hpow (T : ℕ) : (1 : ℝ) ≤ ((p ^ T : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero T (NeZero.ne p)))
  unfold localExcessBeta
  split_ifs
  · rfl
  · linarith [hpow ((∑ u, a u) - rowMaxValuation a)]
  · linarith [hpow ((∑ u, a u) - rowTopTwoSum a)]

theorem one_add_localExcessBeta_le (p : ℕ) [NeZero p] {q : ℕ} (a : Fin q → ℕ) (bad : Prop) :
    1 + localExcessBeta p a bad ≤ ((p ^ (∑ u, a u) : ℕ) : ℝ) := by
  have hpow (T : ℕ) : ((p ^ ((∑ u, a u) - T) : ℕ) : ℝ) ≤ ((p ^ (∑ u, a u) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne p)) (Nat.sub_le (∑ u, a u) T)
  have h1 : (1 : ℝ) ≤ ((p ^ (∑ u, a u) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (NeZero.ne p)))
  unfold localExcessBeta
  split_ifs
  · linarith
  · linarith [hpow (rowMaxValuation a)]
  · linarith [hpow (rowTopTwoSum a)]

theorem primePowerLocalAlpha_excess_le_beta (p q d A : ℕ) [NeZero p]
    (hp : p.Prime) (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A)
    (c : Fin q → Fin d → ℤ) (bad : Prop)
    (hprimitive : ∀ u, ∃ j, (c u j : ZMod p) ≠ 0)
    (hindependent : ¬ bad → ∀ u v, u ≠ v → LinearIndependent (ZMod p)
      ![(fun j => (c u j : ZMod p)), (fun j => (c v j : ZMod p))]) :
    0 ≤ primePowerLocalAlpha p q d A a ha c - 1 ∧
      primePowerLocalAlpha p q d A a ha c - 1 ≤ localExcessBeta p a bad := by
  constructor
  · linarith [(primePowerLocalAlpha_bounds p q d A a ha c).1]
  · by_cases hfew : (positiveRowSet a).card ≤ 1
    · rw [primePowerLocalAlpha_few_positive p q d A hp a ha c hfew hprimitive,
        localExcessBeta_eq_zero_of_few a bad hfew]
      norm_num
    · have htwo : 2 ≤ (positiveRowSet a).card := by omega
      obtain ⟨u, v, hne, _, hmax, hsum, _⟩ := exists_top_two_rows a htwo
      by_cases hb : bad
      · have hu := primePowerLocalAlpha_le_single p q d A hp a ha c u (hprimitive u)
        rw [hmax] at hu
        simp only [localExcessBeta, if_neg hfew, if_pos hb]
        linarith
      · have hu := primePowerLocalAlpha_le_independent_rows p q d A hp a ha c u v
          (hindependent hb u v hne)
        rw [hsum] at hu
        simp only [localExcessBeta, if_neg hfew, if_neg hb]
        linarith

end Hindman168
