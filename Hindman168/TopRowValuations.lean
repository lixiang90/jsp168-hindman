import Hindman168.NormalizedKernelCRT

/-!
# Actual largest two positive row valuations

The largest pair sum is a finite supremum over distinct positive rows.
If at least two valuations are positive, an actual maximizing pair can
be ordered so its first valuation is the global maximum and every other
valuation is no larger than its second. Empty and single-positive arrays
are treated separately.
-/

namespace Hindman168

open scoped BigOperators Classical

def positiveRowSet {q : ℕ} (a : Fin q → ℕ) : Finset (Fin q) :=
  Finset.univ.filter (fun u => 0 < a u)

def positiveRowPairs {q : ℕ} (a : Fin q → ℕ) : Finset (Fin q × Fin q) :=
  ((positiveRowSet a).product (positiveRowSet a)).filter (fun uv => uv.1 ≠ uv.2)

def rowTopTwoSum {q : ℕ} (a : Fin q → ℕ) : ℕ :=
  (positiveRowPairs a).sup (fun uv => a uv.1 + a uv.2)

theorem mem_positiveRowSet {q : ℕ} (a : Fin q → ℕ) (u : Fin q) :
    u ∈ positiveRowSet a ↔ 0 < a u := by simp [positiveRowSet]

theorem mem_positiveRowPairs {q : ℕ} (a : Fin q → ℕ) (u v : Fin q) :
    (u, v) ∈ positiveRowPairs a ↔ 0 < a u ∧ 0 < a v ∧ u ≠ v := by
  simp [positiveRowPairs, mem_positiveRowSet, and_assoc]

theorem positiveRowPairs_nonempty_iff {q : ℕ} (a : Fin q → ℕ) :
    (positiveRowPairs a).Nonempty ↔ 2 ≤ (positiveRowSet a).card := by
  constructor
  · rintro ⟨⟨u, v⟩, huv⟩
    obtain ⟨hu, hv, hne⟩ := (mem_positiveRowPairs a u v).mp huv
    have h := Finset.one_lt_card.mpr ⟨u, (mem_positiveRowSet a u).mpr hu,
      v, (mem_positiveRowSet a v).mpr hv, hne⟩
    omega
  · intro h
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (positiveRowSet a).card)
    exact ⟨(u, v), (mem_positiveRowPairs a u v).mpr
      ⟨(mem_positiveRowSet a u).mp hu, (mem_positiveRowSet a v).mp hv, hne⟩⟩

theorem rowTopTwoSum_le_sum {q : ℕ} (a : Fin q → ℕ) : rowTopTwoSum a ≤ ∑ u, a u := by
  apply Finset.sup_le_iff.mpr
  intro uv huv
  obtain ⟨_, _, hne⟩ := (mem_positiveRowPairs a uv.1 uv.2).mp huv
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({uv.1, uv.2} : Finset (Fin q))) (fun u _ _ => Nat.zero_le (a u))
  simpa only [Finset.sum_pair hne] using h

theorem rowTopTwoSum_eq_zero_of_few_positive {q : ℕ} (a : Fin q → ℕ)
    (h : (positiveRowSet a).card ≤ 1) : rowTopTwoSum a = 0 := by
  have he : positiveRowPairs a = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hn
    have := (positiveRowPairs_nonempty_iff a).mp hn
    omega
  simp only [rowTopTwoSum, he, Finset.sup_empty, bot_eq_zero]

theorem ordered_top_pair_bounds {q : ℕ} (a : Fin q → ℕ) (u v : Fin q)
    (hmem : (u, v) ∈ positiveRowPairs a) (horder : a v ≤ a u)
    (hsum : a u + a v = rowTopTwoSum a) :
    a u = rowMaxValuation a ∧ ∀ i, i ≠ u → a i ≤ a v := by
  obtain ⟨hu, hv, _⟩ := (mem_positiveRowPairs a u v).mp hmem
  have hother (i : Fin q) (hi : i ≠ u) : a i ≤ a v := by
    by_cases hz : 0 < a i
    · have hpair := (mem_positiveRowPairs a u i).mpr ⟨hu, hz, hi.symm⟩
      have hle : a u + a i ≤ rowTopTwoSum a :=
        Finset.le_sup (f := fun uv => a uv.1 + a uv.2) hpair
      omega
    · omega
  have hmax : rowMaxValuation a ≤ a u := by
    apply Finset.sup_le_iff.mpr
    intro i _
    by_cases hi : i = u
    · subst i; rfl
    · exact (hother i hi).trans horder
  exact ⟨le_antisymm (rowValuation_le_max a u) hmax, hother⟩

theorem exists_top_two_rows {q : ℕ} (a : Fin q → ℕ)
    (h : 2 ≤ (positiveRowSet a).card) :
    ∃ u v, u ≠ v ∧ 0 < a v ∧ a u = rowMaxValuation a ∧
      a u + a v = rowTopTwoSum a ∧ ∀ i, i ≠ u → a i ≤ a v := by
  obtain ⟨⟨u, v⟩, hmem, hsum⟩ := Finset.exists_mem_eq_sup
    (positiveRowPairs a) ((positiveRowPairs_nonempty_iff a).mpr h) (fun uv => a uv.1 + a uv.2)
  change rowTopTwoSum a = a u + a v at hsum
  obtain ⟨hu, hv, hne⟩ := (mem_positiveRowPairs a u v).mp hmem
  by_cases ho : a v ≤ a u
  · have hb := ordered_top_pair_bounds a u v hmem ho hsum.symm
    exact ⟨u, v, hne, hv, hb.1, hsum.symm, hb.2⟩
  · have ho' : a u ≤ a v := by omega
    have hmem' := (mem_positiveRowPairs a v u).mpr ⟨hv, hu, hne.symm⟩
    have hs : a v + a u = rowTopTwoSum a := by omega
    have hb := ordered_top_pair_bounds a v u hmem' ho' hs
    exact ⟨v, u, hne.symm, hu, hb.1, hs, hb.2⟩

theorem rowMaxValuation_le_topTwo_of_two_positive {q : ℕ} (a : Fin q → ℕ)
    (h : 2 ≤ (positiveRowSet a).card) : rowMaxValuation a ≤ rowTopTwoSum a := by
  obtain ⟨u, v, _, _, hmax, hsum, _⟩ := exists_top_two_rows a h
  omega

end Hindman168
