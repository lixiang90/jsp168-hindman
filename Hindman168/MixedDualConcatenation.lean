import Hindman168.NestedMixedDualConcatenationStep
import Hindman168.FirstOrderDualConcatenation

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (Q R : ∀ w, AddSubgroup (G w))
  [∀ w, Fintype (Q w)] [∀ w, Fintype (R w)]
  [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))]

/-- Full concatenation of the genuine closed dual spaces, proved by strong
induction on total degree. Both lower containments of the recursive step
are discharged by strictly smaller total degrees. -/
theorem mixedDualHilbert_concatenation_succ
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (d e : ℕ) :
    mixedDualHilbertSubspace p Q (d + 1) U ⊓ mixedDualHilbertSubspace p R (e + 1) U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (d + e + 1) U := by
  have haux : ∀ n : ℕ, ∀ a b : ℕ, a + b = n →
      mixedDualHilbertSubspace p Q (a + 1) U ⊓ mixedDualHilbertSubspace p R (b + 1) U ≤
        mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (a + b + 1) U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hab
      by_cases hn : n = 0
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst a
        subst b
        exact mixedDualHilbert_first_concatenation p Q U hs R
      · have hk : 0 < a + b := by omega
        apply mixedDualHilbert_concatenation_step p U Q R a b (a + b) hU hs hk
        · intro ha
          obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
          have hsm := ih (a' + b) (by omega) a' b rfl
          change mixedDualHilbertSubspace p Q (a' + 1) U ⊓ mixedDualHilbertSubspace p R (b + 1) U ≤
            mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (a' + 1 + b) U
          rw [Nat.add_right_comm a' 1 b]
          exact hsm
        · intro hb
          obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
          have hsm := ih (a + b') (by omega) a b' rfl
          change mixedDualHilbertSubspace p R (b' + 1) U ⊓ mixedDualHilbertSubspace p Q (a + 1) U ≤
            mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (a + (b' + 1)) U
          rw [← Nat.add_assoc]
          intro z hz
          exact hsm ⟨hz.2, hz.1⟩
  exact haux (d + e) d e rfl

/-- Positive-degree form of the subgroup concatenation theorem on the full
completed weighted Haar Hilbert space. No lower containment is a premise. -/
theorem mixedDualHilbert_concatenation
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U ≤
      mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (d + e - 1) U := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  have hdegree : (a + 1) + (b + 1) - 1 = a + b + 1 := by omega
  change mixedDualHilbertSubspace p Q (a + 1) U ⊓ mixedDualHilbertSubspace p R (b + 1) U ≤
    mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) ((a + 1) + (b + 1) - 1) U
  rw [hdegree]
  exact mixedDualHilbert_concatenation_succ p U Q R hU hs a b

end Hindman168
