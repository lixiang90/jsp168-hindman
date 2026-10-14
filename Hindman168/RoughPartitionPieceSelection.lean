import Hindman168.RoughPartitionWeightComparison
import Hindman168.RoughUniformFiberSelection

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem rough_partition_discrepancy_selection {ι : Type*} [Fintype ι]
    (A B a : ι → ℤ) (N K t : ℕ) (hN : 0 < N) (hK : 0 < K)
    (ht : 0 < t) (hcop : t.Coprime K)
    (c Z : ℝ) (hc : 0 < c) (hZ : 0 < Z) (htZ : 2*(t : ℝ) ≤ c*Z)
    (hlen : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (f g : (ι → ℤ) → ℝ) (θ M η : ℝ) (hM : 0 ≤ M)
    (hg : ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)), |g x| ≤ M)
    (hgap : θ + M * (((N ^ Fintype.card ι * K ^ Fintype.card ι : ℕ) : ℝ) *
        Fintype.card ι * (5*(t : ℝ)/(c*Z))) < η)
    (hbad : η ≤ |expectation (uniformFinsetMass (alignmentBoxClass A B a t)) f -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (A j) (B j)))) g|) :
    ∃ p : (ι → Fin N) × (ι → Fin K),
      0 < (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
        alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
          (fun j => ((p.2 j).val : ℤ)) K).card ∧
      θ < |expectation (uniformFinsetMass
          (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1) a t ∩
            alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
              (fun j => ((p.2 j).val : ℤ)) K)) f -
        expectation (uniformFinsetMass
          (alignmentBoxClass (roughBoxLower A B N p.1) (roughBoxUpper A B N p.1)
            (fun j => ((p.2 j).val : ℤ)) K)) g| := by
  have hAB : ∀ j, A j ≤ B j := by
    intro j
    have hh : (A j : ℝ) ≤ B j := by linarith [mul_pos hc hZ, hlen j]
    exact_mod_cast hh
  have hS : 0 < (alignmentBoxClass A B a t).card := by
    apply Finset.card_pos.mpr
    apply alignmentBoxClass_nonempty A B a t ht
    intro j
    have hh : 2*(t : ℝ) ≤ (B j : ℝ)-A j := htZ.trans (hlen j)
    exact_mod_cast hh
  have hw := rough_partition_weight_comparison A B a N K t hN hK ht hcop c Z hc hZ htZ hlen
  have hgap' : θ + M * (∑ p : (ι → Fin N) × (ι → Fin K),
      |(((alignmentBoxClass A B a t).filter (fun x => roughBoxLabel A B N K hN hK x = p)).card : ℝ) /
          (alignmentBoxClass A B a t).card -
        (((Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).filter
          (fun x => roughBoxLabel A B N K hN hK x = p)).card : ℝ) /
          (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))).card|) < η := by
    have hm := mul_le_mul_of_nonneg_left hw hM
    linarith only [hm, hgap]
  have hselect := rough_uniform_fiber_discrepancy_selection
    (α := ι → ℤ) (ι := (ι → Fin N) × (ι → Fin K))
    (alignmentBoxClass A B a t) (Fintype.piFinset (fun j => Finset.Ico (A j) (B j))) hS
    (roughBoxLabel A B N K hN hK) f g θ M η hM
  have hfilter (U : Finset (ι → ℤ)) (p : (ι → Fin N) × (ι → Fin K)) :
      @Finset.filter (ι → ℤ) (fun x => roughBoxLabel A B N K hN hK x = p)
        (fun x => Classical.propDecidable _) U =
      U.filter (fun x => roughBoxLabel A B N K hN hK x = p) := by
    ext x
    simp only [Finset.mem_filter]
  simp_rw [hfilter] at hselect
  have hselect2 := hselect hg
  have hselect3 := hselect2 hgap'
  obtain ⟨p, hp, hdiff⟩ := hselect3 hbad
  have he1 := rough_box_label_fiber A B a N K hN hK hAB (t : ℤ) p
  have he2 := rough_box_unrestricted_label_fiber A B N K hN hK hAB p
  rw [he1] at hp hdiff
  rw [he2] at hdiff
  exact ⟨p, hp, hdiff⟩

end Hindman168
