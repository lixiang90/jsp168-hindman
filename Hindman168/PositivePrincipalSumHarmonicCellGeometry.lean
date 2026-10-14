import Hindman168.PositivePrincipalSumHarmonicCellEvent
import Hindman168.AlignmentLocalLength
import Hindman168.UniformIntervalPairHaar

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem principal_microcell_first_exact (M q : ℕ) (p : ℤ) (r : Fin M)
    (hres : p % M = r.val) :
    alignmentMicrocellFirst (M*q : ℕ) M p =
      (p / (M*q : ℕ)) * (M*q : ℕ) + r.val := by
  have hr : (r.val : ℤ) % M = r.val :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.isLt)
  simp [alignmentMicrocellFirst, alignmentResidueEndpoint, Int.sub_emod,
    Int.mul_emod, Nat.cast_mul, hres, hr]

/-- Exact original microcell-and-residue fiber; cutoff containment is kept
separate and is never inferred from just the length of a generic interval. -/
theorem principal_microcell_fiber_exact (M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (p y : ℤ) (r : Fin M) (hres : p % M = r.val) :
    y ∈ intervalResidueSet ((p / (M*q : ℕ)) * (M*q : ℕ)) (M*q) M r.val ↔
      y / (M*q : ℕ) = p / (M*q : ℕ) ∧ y % M = p % M := by
  have hR : (0 : ℤ) < (M*q : ℕ) := by exact_mod_cast Nat.mul_pos hM hq
  have hy := Int.ediv_mul_le y hR.ne'
  have hy' := Int.lt_ediv_add_one_mul_self y hR
  simp only [intervalResidueSet, integerWindow, Finset.mem_filter, Finset.mem_Ico, hres]
  constructor
  · rintro ⟨⟨hl, hu⟩, hr⟩
    refine ⟨?_, hr⟩
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hh : y / (M*q : ℕ) + 1 ≤ p / (M*q : ℕ) := by omega
      nlinarith
    · have hh : p / (M*q : ℕ) + 1 ≤ y / (M*q : ℕ) := by omega
      nlinarith
  · rintro ⟨he, hr⟩
    rw [he] at hy hy'
    exact ⟨⟨hy, by nlinarith⟩, hr⟩

/-- The actual first-residue-point orbit has precisely the old Fin q
progression mean; endpoints and the number of points are exact. -/
theorem principal_microcell_uniform_event (M q : ℕ) (p : ℤ) (r : Fin M)
    (hres : p % M = r.val) (P : ℤ → Prop) :
    event (uniformIntervalMass 0 q)
      (fun ell => P (alignmentMicrocellFirst (M*q : ℕ) M p + M*ell)) =
      finiteHaarMean (fun t : Fin q => if P
        (completeResidueCellPoint (p / (M*q : ℕ)) M q r t) then 1 else 0) := by
  rw [← uniformFin_cast_interval_law q, event_map, event_eq_expectation,
    uniformFinite_expectation_haar, principal_microcell_first_exact M q p r hres]
  rfl
end Hindman168
