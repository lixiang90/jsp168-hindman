import Hindman168.RoughBalancedBoxGeometry
import Hindman168.RoughFiniteBoxWeightComparison

namespace Hindman168
open scoped BigOperators Classical

theorem rough_box_partition_card {ι : Type*} [Fintype ι] (N K : ℕ) :
    Fintype.card ((ι → Fin N) × (ι → Fin K)) = N ^ Fintype.card ι * K ^ Fintype.card ι := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

theorem rough_partition_weight_comparison {ι : Type*} [Fintype ι]
    (A B a : ι → ℤ) (N K t : ℕ) (hN : 0 < N) (hK : 0 < K)
    (ht : 0 < t) (hcop : t.Coprime K)
    (c Z : ℝ) (hc : 0 < c) (hZ : 0 < Z) (htZ : 2*(t : ℝ) ≤ c*Z)
    (hlen : ∀ j, c*Z ≤ (B j : ℝ)-A j) :
    (∑ p : (ι → Fin N) × (ι → Fin K),
      |(((alignmentBoxClass A B a t).filter
            (fun x => roughBoxLabel A B N K hN hK x = p)).card : ℝ) /
          (alignmentBoxClass A B a t).card -
        (((Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).filter
            (fun x => roughBoxLabel A B N K hN hK x = p)).card : ℝ) /
          (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card|) ≤
      ((N ^ Fintype.card ι * K ^ Fintype.card ι : ℕ) : ℝ) *
        Fintype.card ι * (5*(t : ℝ)/(c*Z)) := by
  have hAB : ∀ j, A j ≤ B j := by
    intro j
    have hh : (A j : ℝ) ≤ B j := by linarith [mul_pos hc hZ, hlen j]
    exact_mod_cast hh
  have hh := rough_finite_box_piece_weights_scaled
    (Finset.univ : Finset ((ι → Fin N) × (ι → Fin K))) A B a
    (fun p => roughBoxLower A B N p.1) (fun p => roughBoxUpper A B N p.1)
    (fun p j => ((p.2 j).val : ℤ)) t K ht hK hcop
    (fun p _ => (rough_balanced_box_contained A B N hN hAB p.1).1)
    (fun p _ => (rough_balanced_box_contained A B N hN hAB p.1).2.1)
    (fun p _ => (rough_balanced_box_contained A B N hN hAB p.1).2.2)
    c Z hc hZ htZ hlen
  simpa only [rough_box_label_fiber A B a N K hN hK hAB,
    rough_box_unrestricted_label_fiber A B N K hN hK hAB,
    Finset.card_univ, rough_box_partition_card] using hh

end Hindman168
