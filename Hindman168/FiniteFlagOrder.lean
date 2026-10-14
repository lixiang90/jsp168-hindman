import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

namespace Hindman168

noncomputable def finiteFlagDepth {k n : ℕ} (P : Fin k → Fin n → Prop) (i : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => P j i)).card

theorem finite_flag_mem_iff_depth {k n : ℕ} (P : Fin k → Fin n → Prop)
    (hP : ∀ i j, i ≤ j → ∀ x, P j x → P i x) (j : Fin k) (x : Fin n) :
    P j x ↔ j.val < finiteFlagDepth P x := by
  classical
  constructor
  · intro h
    have hs : Finset.Iic j ⊆ Finset.univ.filter (fun i => P i x) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP i j (Finset.mem_Iic.mp hi) x h⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact hc
  · intro h
    by_contra hn
    have hs : Finset.univ.filter (fun i => P i x) ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hij
      exact hn (hP j i (le_of_not_gt hij) x (Finset.mem_filter.mp hi).2)
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact (Nat.not_lt_of_ge hc) h

theorem finite_flag_sort_upper {k n : ℕ} (P : Fin k → Fin n → Prop)
    (hP : ∀ i j, i ≤ j → ∀ x, P j x → P i x) (j : Fin k)
    {a b : Fin n} (hab : a ≤ b) :
    P j (Tuple.sort (finiteFlagDepth P) a) → P j (Tuple.sort (finiteFlagDepth P) b) := by
  rw [finite_flag_mem_iff_depth P hP, finite_flag_mem_iff_depth P hP]
  exact fun h => lt_of_lt_of_le h (Tuple.monotone_sort (finiteFlagDepth P) hab)

noncomputable def finiteUpperStart {n : ℕ} (p : Fin n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => ¬ p i)).card

theorem finite_upper_mem_iff_start {n : ℕ} (p : Fin n → Prop)
    (h : ∀ i j, i ≤ j → p i → p j) (i : Fin n) :
    p i ↔ finiteUpperStart p ≤ i.val := by
  classical
  constructor
  · intro hi
    have hs : Finset.univ.filter (fun j => ¬ p j) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact (Finset.mem_filter.mp hj).2 (h i j (le_of_not_gt hji) hi)
    have hc := Finset.card_le_card hs
    rwa [Fin.card_Iio] at hc
  · intro hi
    by_contra hn
    have hs : Finset.Iic i ⊆ Finset.univ.filter (fun j => ¬ p j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hp => hn (h j i (Finset.mem_Iic.mp hj) hp)⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact (Nat.not_lt_of_ge hi) hc

theorem finite_upper_start_le {n : ℕ} (p : Fin n → Prop) : finiteUpperStart p ≤ n := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin n)

end Hindman168
