import Hindman168.CompleteResidueCellPartition

namespace Hindman168
open scoped BigOperators

theorem alignedInterval_residue_partition (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (a b : ℤ) :
    ((Finset.Ico a b).product (Finset.univ : Finset (Fin M))).biUnion
      (fun c => intervalResidueSet (c.1 * R) R M c.2.val) = Finset.Ico (a * R) (b * R) := by
  classical
  have hp : (0 : ℤ) < R := by exact_mod_cast hR
  have hm : (0 : ℤ) < M := by exact_mod_cast hM
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨k, r⟩, hkr, hy⟩
    obtain ⟨hak, hkb⟩ := Finset.mem_Ico.mp (Finset.mem_product.mp hkr).1
    have he := (mem_intervalResidueSet_iff_piece R M hR k r y).mp hy
    have hk : y / R = k := (Prod.mk.inj he).1
    constructor
    · apply (Int.le_ediv_iff_mul_le hp).mp
      simpa [hk] using hak
    · apply (Int.ediv_lt_iff_lt_mul hp).mp
      simpa [hk] using hkb
  · intro hy
    have hr0 := Int.emod_nonneg y (ne_of_gt hm)
    have hrlt := Int.emod_lt_of_pos y hm
    let r : Fin M := ⟨(y % M).toNat, by omega⟩
    refine ⟨(y / R, r), Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_univ r⟩, ?_⟩
    · exact (Int.le_ediv_iff_mul_le hp).mpr hy.1
    · exact (Int.ediv_lt_iff_lt_mul hp).mpr hy.2
    · apply (mem_intervalResidueSet_iff_piece R M hR _ r y).mpr
      apply Prod.ext
      · rfl
      · exact (Int.toNat_of_nonneg hr0).symm

theorem alignedInterval_residue_sum (R M : ℕ) (hR : 0 < R) (hM : 0 < M)
    (a b : ℤ) (F : ℤ → ℝ) :
    (∑ y ∈ Finset.Ico (a * R) (b * R), F y) =
      ∑ k ∈ Finset.Ico a b, ∑ r : Fin M,
        ∑ y ∈ intervalResidueSet (k * R) R M r.val, F y := by
  rw [← alignedInterval_residue_partition R M hR hM a b,
    intervalResidueSet_union_sum R M hR]
  exact Finset.sum_product _ _ _

end Hindman168
