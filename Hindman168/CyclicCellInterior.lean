import Hindman168.CyclicCellCoordinates

namespace Hindman168
open scoped BigOperators

theorem cyclicCell_product_eq_of_interior {ι : Type*} (S : Finset ι)
    (k : ℤ) (M q H : ℕ) [NeZero q] (r : Fin M) (z : ZMod q)
    (h : ι → ℤ) (hh : ∀ i ∈ S, |h i| ≤ (H : ℤ))
    (hl : H ≤ z.val) (hu : z.val + H < q) (f : ℤ → ℝ) :
    (∏ i ∈ S, f (k * (M * q : ℕ) + r.val + (M : ℤ) * (z + (h i : ZMod q)).val)) =
      ∏ i ∈ S, f (k * (M * q : ℕ) + r.val + (M : ℤ) * z.val + M * h i) := by
  apply Finset.prod_congr rfl
  intro i hi
  obtain ⟨ha, hb⟩ := abs_le.mp (hh i hi)
  have hlo : 0 ≤ (z.val : ℤ) + h i := by omega
  have hhi : (z.val : ℤ) + h i < q := by omega
  rw [zmod_add_val_of_no_wrap q z (h i) hlo hhi]
  congr 1
  ring

theorem cyclic_boundary_card (q H : ℕ) [NeZero q] :
    ((Finset.univ : Finset (ZMod q)).filter (fun z => ¬ (H ≤ z.val ∧ z.val + H < q))).card ≤ 2 * H := by
  classical
  let B := (Finset.univ : Finset (ZMod q)).filter (fun z => ¬ (H ≤ z.val ∧ z.val + H < q))
  change B.card ≤ _
  by_cases hh : H ≤ q
  · have hs : B.image ZMod.val ⊆ Finset.range H ∪ Finset.Ico (q - H) q := by
      intro n hn
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
      have hb := (Finset.mem_filter.mp hz).2
      have hq := z.val_lt
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hc : (B.image ZMod.val).card = B.card := Finset.card_image_of_injective _ (ZMod.val_injective q)
    calc
      B.card = (B.image ZMod.val).card := hc.symm
      _ ≤ (Finset.range H ∪ Finset.Ico (q - H) q).card := Finset.card_le_card hs
      _ ≤ (Finset.range H).card + (Finset.Ico (q - H) q).card := Finset.card_union_le _ _
      _ = 2 * H := by simp; omega
  · have hc : B.card ≤ q := by
      have he := Finset.card_le_card (Finset.filter_subset (fun z : ZMod q => ¬ (H ≤ z.val ∧ z.val + H < q)) Finset.univ)
      simpa only [Finset.card_univ, ZMod.card] using he
    omega

end Hindman168
