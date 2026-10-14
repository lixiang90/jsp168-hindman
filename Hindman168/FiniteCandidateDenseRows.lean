import Hindman168.FiniteRealDenseWeights
import Mathlib.Combinatorics.Pigeonhole

namespace Hindman168
open scoped BigOperators Classical

theorem finite_candidate_origin_count_le_sum {X C : Type*}
    (S : Finset X) (A : Finset C) (R : C → X → Prop) :
    (S.filter (fun x => ∃ c ∈ A, R c x)).card ≤ ∑ c ∈ A, (S.filter (R c)).card := by
  have h : S.filter (fun x => ∃ c ∈ A, R c x) = A.biUnion (fun c => S.filter (R c)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [h]
  exact Finset.card_biUnion_le

/-- The same candidate works for many rows, with many true witnesses in each
row. Candidate existence in a dense set of each row is an explicit input. -/
theorem finite_candidate_dense_rows {Q X C : Type*}
    (T : Finset Q) (S : Finset X) (A : Finset C)
    (hT : T.Nonempty) (hS : S.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (R : C → Q → X → Prop)
    (hrows : ∀ q ∈ T, δ*(S.card : ℝ) ≤
      ((S.filter (fun x => ∃ c ∈ A, R c q x)).card : ℝ)) :
    ∃ c ∈ A, δ/(2*(A.card : ℝ))*(T.card : ℝ) ≤
      ((T.filter (fun q => δ/(2*(A.card : ℝ))*(S.card : ℝ) ≤
        ((S.filter (R c q)).card : ℝ))).card : ℝ) := by
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hA : A.Nonempty := by
    obtain ⟨q, hq⟩ := hT
    have hg : (0 : ℝ) < ((S.filter (fun x => ∃ c ∈ A, R c q x)).card : ℝ) :=
      lt_of_lt_of_le (mul_pos hδ hSc) (hrows q hq)
    have hgn : 0 < (S.filter (fun x => ∃ c ∈ A, R c q x)).card := by exact_mod_cast hg
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hgn
    obtain ⟨c, hc, _⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨c, hc⟩
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have htotal : δ*(T.card : ℝ)*(S.card : ℝ) ≤
      ∑ c ∈ A, ∑ q ∈ T, ((S.filter (R c q)).card : ℝ) := by
    calc
      _ = ∑ q ∈ T, δ*(S.card : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ q ∈ T, ∑ c ∈ A, ((S.filter (R c q)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        refine (hrows q hq).trans ?_
        exact_mod_cast finite_candidate_origin_count_le_sum S A (fun c x => R c q x)
      _ = _ := Finset.sum_comm
  have havg : (∑ c ∈ A, δ/(A.card : ℝ)*(T.card : ℝ)*(S.card : ℝ)) ≤
      ∑ c ∈ A, ∑ q ∈ T, ((S.filter (R c q)).card : ℝ) := by
    have heq : (∑ c ∈ A, δ/(A.card : ℝ)*(T.card : ℝ)*(S.card : ℝ)) =
        δ*(T.card : ℝ)*(S.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [heq]
    exact htotal
  obtain ⟨c, hc, hmean⟩ := Finset.exists_le_of_sum_le hA havg
  have hd := finite_real_sum_dense_large_weights T
    (fun q => ((S.filter (R c q)).card : ℝ)) (S.card : ℝ) (δ/(A.card : ℝ))
    hSc (div_nonneg hδ.le hAc.le)
    (fun q _ => by exact_mod_cast Finset.card_filter_le S (R c q)) hmean
  have heq : δ/(A.card : ℝ)/2 = δ/(2*(A.card : ℝ)) := by ring
  have heq2 : δ/(A.card : ℝ)*(S.card : ℝ)/2 = δ/(2*(A.card : ℝ))*(S.card : ℝ) := by ring
  refine ⟨c, hc, ?_⟩
  simpa only [heq, heq2] using hd

end Hindman168
