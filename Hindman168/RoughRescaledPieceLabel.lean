import Hindman168.RoughBoxPartition
import Hindman168.RoughBalancedBoxGeometry
import Hindman168.RoughResidueBoxTransport

namespace Hindman168
open scoped Classical

theorem rough_rescaled_piece_label {ι : Type*} [Fintype ι]
    (A B : ι → ℤ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hAB : ∀ j, A j ≤ B j) (p : (ι → Fin N) × (ι → Fin K))
    (y : ι → ℤ)
    (hy : y ∈ Fintype.piFinset (fun j =>
      Finset.Ico
        (roughResidueBoxEndpoint (roughBoxLower A B N p.1) (fun j => (p.2 j).val) K j)
        (roughResidueBoxEndpoint (roughBoxUpper A B N p.1) (fun j => (p.2 j).val) K j))) :
    roughBoxLabel A B N K hN hK (roughResidueBoxAffine (fun j => (p.2 j).val) K y) = p := by
  have hp : (0 : ℤ) < K := by exact_mod_cast hK
  have hx : roughResidueBoxAffine (fun j => (p.2 j).val) K y ∈
      alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
        (fun j => (p.2 j).val) K := by
    rw [← rough_residue_box_unrestricted_image _ _ _ K hp]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  rw [← rough_box_unrestricted_label_fiber A B N K hN hK hAB p] at hx
  exact (Finset.mem_filter.mp hx).2

theorem rough_rescaled_piece_test {ι : Type*} [Fintype ι] {X : Type*}
    (A B : ι → ℤ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hAB : ∀ j, A j ≤ B j) (p : (ι → Fin N) × (ι → Fin K))
    (g : ((ι → Fin N) × (ι → Fin K)) → X → ℝ) (Q : (ι → ℤ) → X)
    (y : ι → ℤ)
    (hy : y ∈ Fintype.piFinset (fun j =>
      Finset.Ico
        (roughResidueBoxEndpoint (roughBoxLower A B N p.1) (fun j => (p.2 j).val) K j)
        (roughResidueBoxEndpoint (roughBoxUpper A B N p.1) (fun j => (p.2 j).val) K j))) :
    g (roughBoxLabel A B N K hN hK (roughResidueBoxAffine (fun j => (p.2 j).val) K y))
        (Q (roughResidueBoxAffine (fun j => (p.2 j).val) K y)) =
      g p (Q (roughResidueBoxAffine (fun j => (p.2 j).val) K y)) := by
  rw [rough_rescaled_piece_label A B N K hN hK hAB p y hy]

end Hindman168
