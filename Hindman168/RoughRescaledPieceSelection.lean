import Hindman168.RoughFrozenPartitionSelection
import Hindman168.RoughResidueBoxSampling

namespace Hindman168
open FiniteMass
open scoped Classical

theorem rough_frozen_rescaled_piece_selection {ι : Type*} [Fintype ι]
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
    ∃ (p : (ι → Fin N) × (ι → Fin K)) (v : ι → ℤ),
      let u : ι → ℤ := fun j => (p.2 j).val
      let l := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
      let r := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
      0 < (alignmentBoxClass l r v t).card ∧
      0 < (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))).card ∧
      θ < |expectation (uniformFinsetMass (alignmentBoxClass l r v t))
          (fun y => approx (roughResidueBoxAffine u K y)) -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))))
          (fun y => approx (roughResidueBoxAffine u K y))| := by
  obtain ⟨p, hp, hb⟩ := rough_frozen_partition_selection A B a N K t hN hK ht hcop
    c Z hc hZ htZ hlen f frozen approx θ M η εfreeze εapprox hM happrox hf ha hgap hbad
  let u : ι → ℤ := fun j => (p.2 j).val
  let l := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
  let r := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
  obtain ⟨v, hv⟩ := rough_residue_box_step_push
    (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a u t K ht hK hcop
  have htnew : total (uniformFinsetMass (alignmentBoxClass l r v t)) = 1 := by
    have hh := congrArg total hv
    rw [total_push, uniformFinsetMass_total _ hp] at hh
    exact hh
  have hpos : 0 < (alignmentBoxClass l r v t).card := by
    by_contra hh
    have he : alignmentBoxClass l r v t = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [uniformFinsetMass, he, flatMass_total] at htnew
    norm_num at htnew
  have hsub : alignmentBoxClass l r v t ⊆ Fintype.piFinset (fun j => Finset.Ico (l j) (r j)) := by
    intro y hy
    exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hy j)).1)
  refine ⟨p, v, hpos, hpos.trans_le (Finset.card_le_card hsub), ?_⟩
  have hk : (0 : ℤ) < K := by exact_mod_cast hK
  rw [← hv, ← rough_residue_box_uniform_push
    (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) u K hk,
    expectation_push, expectation_push] at hb
  exact hb

end Hindman168
