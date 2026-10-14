import Hindman168.FiniteScaleLists
import Hindman168.MasterScales

/-! The paper's one-based weights 2^(n-j) on the actual zero-based
principal index set, with strict domination of every later subset. -/

namespace Hindman168
open scoped BigOperators Classical

def alignmentSubsetWeight {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  ∑ j ∈ S, 2 ^ (n - 1 - j.val)

theorem alignmentSubsetWeight_binary {n : ℕ} (S : Finset (Fin n)) :
    alignmentSubsetWeight S = binaryWeight (S.image (fun j => n - 1 - j.val)) := by
  unfold alignmentSubsetWeight binaryWeight
  rw [Finset.sum_image]
  intro a _ b _ hab
  change n - 1 - a.val = n - 1 - b.val at hab
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem alignmentSubsetWeight_separation {n : ℕ} (A B : Finset (Fin n))
    (p : Fin n) (hp : p ∈ A) (hbefore : ∀ b ∈ B, p < b) :
    alignmentSubsetWeight B < alignmentSubsetWeight A := by
  rw [alignmentSubsetWeight_binary, alignmentSubsetWeight_binary]
  apply binary_weight_separation (k := n - 1 - p.val)
  · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · intro j hj
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    have hpb := hbefore b hb
    have hpN := p.isLt
    have hbN := b.isLt
    change p.val < b.val at hpb
    omega

theorem alignmentSubsetWeight_positive {n : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) : 0 < alignmentSubsetWeight S := by
  obtain ⟨p, hp⟩ := hS
  have h := Finset.single_le_sum (fun j _ => Nat.zero_le (2 ^ (n - 1 - j.val))) hp
  exact lt_of_lt_of_le (Nat.pow_pos (by decide)) h

end Hindman168
