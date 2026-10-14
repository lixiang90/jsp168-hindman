import Hindman168.RoughRescaledPieceLabel

namespace Hindman168
open scoped Classical

theorem rough_rescaled_dependent_piece_test {ι : Type*} [Fintype ι]
    (A B : ι → ℤ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hAB : ∀ j, A j ≤ B j) (p : (ι → Fin N) × (ι → Fin K))
    (X : ((ι → Fin N) × (ι → Fin K)) → Type*)
    (g : ∀ p, X p → ℝ) (Q : ∀ p, (ι → ℤ) → X p)
    (y : ι → ℤ)
    (hy : y ∈ Fintype.piFinset (fun j =>
      Finset.Ico
        (roughResidueBoxEndpoint (roughBoxLower A B N p.1) (fun j => (p.2 j).val) K j)
        (roughResidueBoxEndpoint (roughBoxUpper A B N p.1) (fun j => (p.2 j).val) K j))) :
    let x := roughResidueBoxAffine (fun j => (p.2 j).val) K y
    g (roughBoxLabel A B N K hN hK x) (Q (roughBoxLabel A B N K hN hK x) x) = g p (Q p x) := by
  intro x
  have he := rough_rescaled_piece_label A B N K hN hK hAB p y hy
  change roughBoxLabel A B N K hN hK x = p at he
  rw [he]

end Hindman168
