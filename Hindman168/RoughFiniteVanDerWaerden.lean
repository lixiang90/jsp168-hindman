import Mathlib.Combinatorics.HalesJewett
import Hindman168.RoughFractionalColor

namespace Hindman168
open scoped BigOperators

theorem rough_finite_van_der_waerden (H : ℕ) (hH : 0 < H) (κ : Type*) [Finite κ] :
    ∃ N : ℕ, 0 < N ∧ ∀ C : ℕ → κ, ∃ a b : ℕ, ∃ c : κ,
      0 < b ∧ b ≤ N ∧ ∀ z : ℕ, z < H → a + b * z < N ∧ C (a + b * z) = c := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin H) κ
  refine ⟨Fintype.card ι * H + 1, by omega, ?_⟩
  intro C
  obtain ⟨l, c, hl⟩ := hι (fun v => C (∑ i, (v i).val))
  let s : Finset ι := {i | l.idxFun i = none}
  let a := ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0
  have hspos : 0 < s.card := by
    apply Finset.card_pos.mpr
    exact ⟨l.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  have hsum : ∀ z : Fin H, (∑ i, (l z i).val) = s.card * z.val + a := by
    intro z
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · calc
        _ = ∑ _i ∈ s, z.val := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [l.apply_none _ _ (Finset.mem_filter.mp hi).2]
        _ = _ := by simp
    · apply Finset.sum_congr rfl
      intro i hi
      have hn : l.idxFun i ≠ none := by
        intro he
        exact Finset.mem_compl.mp hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hn
      simp [← hy]
  refine ⟨a, s.card, c, hspos, ?_, ?_⟩
  · have hs : s.card ≤ Fintype.card ι := Finset.card_le_univ s
    have hm : Fintype.card ι ≤ Fintype.card ι * H := Nat.le_mul_of_pos_right _ hH
    omega
  · intro z hz
    have he := hsum ⟨z, hz⟩
    have hb : (∑ i, (l ⟨z, hz⟩ i).val) ≤ Fintype.card ι * H := by
      calc
        _ ≤ ∑ _i : ι, H := Finset.sum_le_sum (fun i _ => (l ⟨z, hz⟩ i).isLt.le)
        _ = _ := by simp
    constructor
    · dsimp only at he
      omega
    · simpa only [hsum, Nat.add_comm] using hl ⟨z, hz⟩

end Hindman168
