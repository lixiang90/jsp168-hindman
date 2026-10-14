import Hindman168.MaskRowInvariance

/-!
# The paper's coordinate choice for every mask support

If the tracked support has a coordinate outside the mask, insert there.
Otherwise take two distinct coordinates of the tracked support inside the
mask, for the balanced reciprocal substitution. Its absorbed branches have
at most one column per fresh variable. This choice uses only the two finite
supports, and always leaves the tracked row noninvariant.
-/

namespace Hindman168

open scoped BigOperators Classical

inductive MaskColumnPlan {m : ℕ} (S U : Finset (Fin (m + 1))) where
  | outside (u : Fin (m + 1)) (hu : u ∈ S) (hU : u ∉ U)
  | balanced (u v : Fin (m + 1)) (hu : u ∈ S) (hv : v ∈ S)
      (huU : u ∈ U) (hvU : v ∈ U) (hne : u ≠ v)

theorem exists_maskColumnPlan {m : ℕ} (S U : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) :
    Nonempty (MaskColumnPlan S U) := by
  by_cases hout : ∃ u ∈ S, u ∉ U
  · obtain ⟨u, hu, hU⟩ := hout
    exact ⟨MaskColumnPlan.outside u hu hU⟩
  · have hsub : S ⊆ U := by
      intro u hu
      by_contra hU
      exact hout ⟨u, hu, hU⟩
    obtain ⟨u, hu, v, hv, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    exact ⟨MaskColumnPlan.balanced u v hu hv (hsub hu) (hsub hv) hne⟩

noncomputable def chosenMaskColumnPlan {m : ℕ}
    (S U : Finset (Fin (m + 1))) (hS : 2 ≤ S.card) : MaskColumnPlan S U :=
  Classical.choice (exists_maskColumnPlan S U hS)

def MaskColumnPlan.tag {m : ℕ} {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) :
    Fin (m + 1) → Fin 3 :=
  match P with
  | .outside u _ _ => fun k => if k = u then 1 else 0
  | .balanced u v _ _ _ _ _ => fun k => if k = u then 1 else if k = v then 2 else 0

theorem MaskColumnPlan.tag_separates {m : ℕ} {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (hS : 2 ≤ S.card) :
    ∃ j ∈ S, ∃ k ∈ S, P.tag j ≠ P.tag k := by
  cases P with
  | outside u hu hU =>
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    by_cases hua : u = a
    · refine ⟨u, hu, b, hb, ?_⟩
      have hbu : b ≠ u := by intro h; exact hab (hua.symm.trans h.symm)
      simp [MaskColumnPlan.tag, hbu]
    · refine ⟨u, hu, a, ha, ?_⟩
      simp [MaskColumnPlan.tag, Ne.symm hua]
  | balanced u v hu hv huU hvU hne =>
    exact ⟨u, hu, v, hv, by simp [MaskColumnPlan.tag, Ne.symm hne]⟩

theorem MaskColumnPlan.tag_unique_nonzero {m : ℕ} {S U : Finset (Fin (m + 1))}
    (P : MaskColumnPlan S U) (j k : Fin (m + 1)) (he : P.tag j = P.tag k)
    (hn : P.tag j ≠ 0) : j = k := by
  cases P <;> dsimp only [MaskColumnPlan.tag] at he hn
  all_goals split_ifs at he hn <;> simp_all

theorem MaskColumnPlan.tracked_noninvariant {R : Type*} [Zero R] {m : ℕ}
    {S U : Finset (Fin (m + 1))} (P : MaskColumnPlan S U) (hS : 2 ≤ S.card)
    (A : Fin (m + 1) → R) (hA : ∀ k, A k ≠ 0 ↔ k ∈ S) : ¬ maskRowInvariant A P.tag := by
  obtain ⟨j, hj, k, hk, ht⟩ := P.tag_separates hS
  intro hi
  exact ht (hi j k ((hA j).mpr hj) ((hA k).mpr hk))

end Hindman168
