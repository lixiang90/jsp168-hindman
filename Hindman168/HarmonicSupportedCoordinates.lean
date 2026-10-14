import Hindman168.MaskTargetAnchorComparison

/-! Original harmonic supports bound earlier coordinates. No upper bound
is needed for coordinates strictly above the normalization anchor. -/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem piMass_mem_support_coordinate {ι : Type*} [Fintype ι] {α : ι → Type*}
    (μ : ∀ i, Mass (α i)) (z : ∀ i, α i) (hz : z ∈ (piMass μ).support) (i : ι) :
    z i ∈ (μ i).support := by
  have hn := Finsupp.mem_support_iff.mp hz
  rw [piMass_apply] at hn
  exact Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ i))

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem integerMass_support_natAbs_le (X W : ℕ) (z : ℤ) (hz : z ∈ (integerMass X W).support) :
    z.natAbs ≤ X ^ 2 := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hz)
  have hw : n ∈ harmonicWindow X W :=
    (intervalMass_support X (X ^ 2 : ℕ) W _).trans (unitInterval_raw X W).subset hn
  have hb : n < X ^ 2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2
  simpa only [Int.natAbs_natCast] using hb.le

theorem MasterParameterConditions.earlier_cutoff_sq_le_auxiliary
    {n N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (w i j : ℕ) (hij : i < j) :
    F.cutoff w i ^ 2 ≤ F.auxiliary w j := by
  have hs : ({i} : Finset ℕ) ⊆ Finset.range j := by
    intro k hk
    have he : k = i := Finset.mem_singleton.mp hk
    subst k
    exact Finset.mem_range.mpr hij
  simpa only [Finset.prod_singleton] using hF.earlier_tail_product_bound w j {i} hs

namespace MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def rootRestMass (w : ℕ) : Mass ({col : Fin (m + 1) // col ≠ targetRootAnchor gap t} → ℤ) :=
  piMass (fun col => integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col.val)) (primorial w))

theorem rootRestMass_support_before_anchor (w : ℕ)
    (rest : {col : Fin (m + 1) // col ≠ targetRootAnchor gap t} → ℤ)
    (hr : rest ∈ (rootRestMass gap C t w).support)
    (col : {col : Fin (m + 1) // col ≠ targetRootAnchor gap t}) (hcol : col.val < targetRootAnchor gap t) :
    (rest col).natAbs ≤ (maskGeneratedMaster m gap).auxiliary w ((C w).pivot (targetRootAnchor gap t)) := by
  have hm := piMass_mem_support_coordinate _ rest hr col
  have hb := integerMass_support_natAbs_le _ _ _ hm
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  exact hb.trans (hF.earlier_cutoff_sq_le_auxiliary w _ _ ((C w).pivot_strictMono hcol))

end MaskOriginalSampling
end Hindman168
