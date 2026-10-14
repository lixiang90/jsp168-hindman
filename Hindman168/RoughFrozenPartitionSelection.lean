import Hindman168.RoughPartitionPieceSelection
import Hindman168.RoughFrozenApproximateDiscrepancy

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem rough_frozen_partition_selection {ι : Type*} [Fintype ι]
    (A B a : ι → ℤ) (N K t : ℕ) (hN : 0 < N) (hK : 0 < K)
    (ht : 0 < t) (hcop : t.Coprime K)
    (c Z : ℝ) (hc : 0 < c) (hZ : 0 < Z) (htZ : 2*(t : ℝ) ≤ c*Z)
    (hlen : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (f frozen approx : (ι → ℤ) → ℝ) (θ M η εfreeze εapprox : ℝ) (hM : 0 ≤ M)
    (happrox : ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)), |approx x| ≤ M)
    (hf : ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)), |f x-frozen x| ≤ εfreeze)
    (ha : ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)), |frozen x-approx x| ≤ εapprox)
    (hgap : θ + M * (((N ^ Fintype.card ι * K ^ Fintype.card ι : ℕ) : ℝ) *
        Fintype.card ι * (5*(t : ℝ)/(c*Z))) + 2*(εfreeze+εapprox) < η)
    (hbad : η ≤ |expectation (uniformFinsetMass (alignmentBoxClass A B a t)) f -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (A j) (B j)))) f|) :
    ∃ p : (ι → Fin N) × (ι → Fin K),
      0 < (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
        alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
          (fun j => ((p.2 j).val : ℤ)) K).card ∧
      θ < |expectation (uniformFinsetMass
          (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
            alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
              (fun j => ((p.2 j).val : ℤ)) K)) approx -
        expectation (uniformFinsetMass
          (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
            (fun j => ((p.2 j).val : ℤ)) K)) approx| := by
  have hS : 0 < (alignmentBoxClass A B a t).card := by
    apply Finset.card_pos.mpr
    apply alignmentBoxClass_nonempty A B a t ht
    intro j
    have hh : 2*(t : ℝ) ≤ (B j : ℝ)-A j := htZ.trans (hlen j)
    exact_mod_cast hh
  have hsub : alignmentBoxClass A B a t ⊆ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)) := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hx j)).1)
  have hT : 0 < (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card :=
    hS.trans_le (Finset.card_le_card hsub)
  have hb := rough_frozen_approximated_discrepancy
    (uniformFinsetMass (alignmentBoxClass A B a t))
    (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))))
    (uniformFinsetMass_nonneg _) (uniformFinsetMass_nonneg _)
    (uniformFinsetMass_total _ hS) (uniformFinsetMass_total _ hT)
    f frozen approx η εfreeze εapprox
    (fun x hx => hf x (hsub (flatMass_support _ _ hx)))
    (fun x hx => hf x (flatMass_support _ _ hx))
    (fun x hx => ha x (hsub (flatMass_support _ _ hx)))
    (fun x hx => ha x (flatMass_support _ _ hx)) hbad
  apply rough_partition_discrepancy_selection A B a N K t hN hK ht hcop c Z hc hZ htZ hlen
    approx approx θ M (η-2*(εfreeze+εapprox)) hM happrox _ hb
  linarith only [hgap]

end Hindman168
