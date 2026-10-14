import Hindman168.RoughIntervalPieceComparison
import Hindman168.RoughProbabilityProductError
import Hindman168.AlignmentBoxMeans

namespace Hindman168
open scoped BigOperators Classical

theorem rough_interval_class_subwindow (A B l r a d : ℤ)
    (hAl : A ≤ l) (hrB : r ≤ B) :
    alignmentIntervalClass l r d a ⊆ alignmentIntervalClass A B d a := by
  intro x hx
  simp only [alignmentIntervalClass, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
  exact ⟨⟨hAl.trans hx.1.1, hx.1.2.trans_le hrB⟩, hx.2⟩

theorem rough_finset_card_ratio_bound {α : Type*} (S T : Finset α) (hST : S ⊆ T) :
    |(S.card : ℝ) / T.card| ≤ 1 := by
  rw [abs_of_nonneg (by positivity : 0 ≤ (S.card : ℝ) / T.card)]
  by_cases ht : T.card = 0
  · simp [ht]
  · have htpos : (0 : ℝ) < T.card := by exact_mod_cast Nat.pos_of_ne_zero ht
    apply (div_le_one htpos).mpr
    exact_mod_cast Finset.card_le_card hST

theorem rough_box_class_intersection_card {ι : Type*} [Fintype ι]
    (l r a u : ι → ℤ) (t K : ℤ) :
    (alignmentBoxClass l r a t ∩ alignmentBoxClass l r u K).card =
      ∏ j, (alignmentIntervalClass (l j) (r j) t (a j) ∩
        alignmentIntervalClass (l j) (r j) K (u j)).card := by
  classical
  have he : alignmentBoxClass l r a t ∩ alignmentBoxClass l r u K =
      Fintype.piFinset (fun j => alignmentIntervalClass (l j) (r j) t (a j) ∩
        alignmentIntervalClass (l j) (r j) K (u j)) := by
    ext x
    simp only [Finset.mem_inter, alignmentBoxClass, Fintype.mem_piFinset]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  rw [he]
  exact Fintype.card_piFinset _

theorem rough_box_piece_weight_difference {ι : Type*} [Fintype ι]
    (A B l r a u : ι → ℤ) (t K : ℕ) (ht : 0 < t) (hK : 0 < K)
    (hcop : t.Coprime K) (hAl : ∀ j, A j ≤ l j) (hlr : ∀ j, l j ≤ r j)
    (hrB : ∀ j, r j ≤ B j) (hlen : ∀ j, 2 * (t : ℝ) ≤ (B j : ℝ) - A j) :
    |((alignmentBoxClass l r a t ∩ alignmentBoxClass l r u K).card : ℝ) /
        (alignmentBoxClass A B a t).card -
      ((alignmentBoxClass l r u K).card : ℝ) /
        (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card| ≤
      ∑ j, 5 * (t : ℝ) / ((B j : ℝ) - A j) := by
  classical
  rw [rough_box_class_intersection_card, alignmentBoxClass_card,
    alignmentBoxClass_card, Fintype.card_piFinset]
  simp only [Nat.cast_prod]
  rw [← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  apply rough_unit_product_error
  · intro j
    apply rough_finset_card_ratio_bound
    exact Finset.Subset.trans Finset.inter_subset_left
      (rough_interval_class_subwindow _ _ _ _ _ _ (hAl j) (hrB j))
  · intro j
    apply rough_finset_card_ratio_bound
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hI := Finset.mem_Ico.mp hx'.1
    exact Finset.mem_Ico.mpr ⟨(hAl j).trans hI.1, hI.2.trans_le (hrB j)⟩
  · intro j
    exact rough_interval_piece_weight_difference _ _ _ _ _ _ t K ht hK hcop
      (hAl j) (hlr j) (hrB j) (hlen j)

end Hindman168
