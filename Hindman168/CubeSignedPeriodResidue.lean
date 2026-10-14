import Hindman168.AlignmentBoxMeans
import Hindman168.SignedProgressionResidue

/-! Every original cube vertex has exactly the common base residue. -/
namespace Hindman168
open scoped BigOperators

theorem cube_signed_period_residue {d M : ℕ} (hM : 0 < M)
    (lo hi v : Fin (d+1) → ℤ) (t : ℤ) (hMt : (M : ℤ) ∣ t)
    (hv : ∀ i : Fin d, (M : ℤ) ∣ v i.succ)
    (x : Fin (d+1) → ℤ) (hx : x ∈ alignmentBoxClass lo hi v t)
    (V : Finset (Fin d)) :
    signedPeriodResidue M hM (x 0 + ∑ i ∈ V, x i.succ) = signedPeriodResidue M hM (v 0) := by
  classical
  have hz : ∀ j, Int.ModEq (M : ℤ) (v j) (x j) := by
    intro j
    have hx' : ∀ j, x j ∈ alignmentIntervalClass (lo j) (hi j) t (v j) := by
      simpa only [alignmentBoxClass, Fintype.mem_piFinset] using hx
    exact ((Finset.mem_filter.mp (hx' j)).2).of_dvd hMt
  have hs : Int.ModEq (M : ℤ) 0 (∑ i ∈ V, x i.succ) := by
    induction V using Finset.induction_on with
    | empty => simp
    | @insert i V hi ih =>
      rw [Finset.sum_insert hi]
      have hv' : Int.ModEq (M : ℤ) 0 (v i.succ) := Int.modEq_iff_dvd.mpr (by simpa using hv i)
      simpa only [zero_add] using (hv'.trans (hz i.succ)).add ih
  apply signed_period_residue_eq_of_modEq M hM
  simpa only [add_zero] using ((hz 0).add hs).symm

end Hindman168
