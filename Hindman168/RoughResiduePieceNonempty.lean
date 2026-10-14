import Hindman168.RoughBoxPieceWeights

namespace Hindman168
open scoped Classical

theorem rough_coprime_interval_piece_nonempty (l r a u : ℤ) (t K : ℕ)
    (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hlen : 2 * ((t * K : ℕ) : ℤ) ≤ r - l) :
    (alignmentIntervalClass l r t a ∩ alignmentIntervalClass l r K u).Nonempty := by
  obtain ⟨c, hc⟩ := rough_coprime_interval_class_intersection l r a u t K hcop
  rw [hc]
  exact alignment_interval_class_nonempty l r c (t * K) (Nat.mul_pos ht hK) hlen

theorem rough_coprime_box_piece_nonempty {ι : Type*} [Fintype ι]
    (l r a u : ι → ℤ) (t K : ℕ) (ht : 0 < t) (hK : 0 < K) (hcop : t.Coprime K)
    (hlen : ∀ j, 2 * ((t * K : ℕ) : ℤ) ≤ r j - l j) :
    (alignmentBoxClass l r a t ∩ alignmentBoxClass l r u K).Nonempty := by
  classical
  have hh : ∀ j, ∃ x : ℤ, x ∈ alignmentIntervalClass (l j) (r j) t (a j) ∩
      alignmentIntervalClass (l j) (r j) K (u j) :=
    fun j => rough_coprime_interval_piece_nonempty _ _ _ _ t K ht hK hcop (hlen j)
  choose x hx using hh
  refine ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_inter.mp (hx j)).1)
  · exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_inter.mp (hx j)).2)

end Hindman168
