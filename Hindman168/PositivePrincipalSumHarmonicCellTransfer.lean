import Hindman168.PositivePrincipalSumHarmonicCellGeometry
import Hindman168.AlignmentShortCutoffProbability

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical

/-- Exact microcell/residue exposure used in (8.12), on signed pivot values. -/
def principalMicrocellExposure (R M : ℕ) (p : ℤ) : ℤ × ℤ := (p / R, p % M)

theorem principal_microcell_harmonic_event_error
    (X W M q : ℕ) (p : ℤ) (r : Fin M)
    (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hWM : W ∣ M)
    (hr : r.val.Coprime W) (hres : p % M = r.val) (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ (p / (M*q : ℕ)) * (M*q : ℕ))
    (hhi : (p / (M*q : ℕ)) * (M*q : ℕ) + (M*q : ℕ) ≤ (X ^ 2 : ℕ)) (P : ℤ → Prop) :
    |event (conditionMass (integerMass X W)
      (fun z => principalMicrocellExposure (M*q) M z = principalMicrocellExposure (M*q) M p)) P -
      event (uniformIntervalMass 0 q)
        (fun ell => P (alignmentMicrocellFirst (M*q : ℕ) M p + M*ell))| ≤
      (M*q : ℕ) / (X : ℝ) := by
  rw [principal_microcell_uniform_event M q p r hres]
  have hf : (fun z => principalMicrocellExposure (M*q) M z = principalMicrocellExposure (M*q) M p) =
      (fun z => z ∈ intervalResidueSet ((p / (M*q : ℕ)) * (M*q : ℕ)) (M*q) M r.val) := by
    funext z
    simp only [principalMicrocellExposure, Prod.mk.injEq]
    exact propext (principal_microcell_fiber_exact M q hM hq p z r hres).symm
  rw [hf]
  exact principal_complete_cell_harmonic_event_error X W M q _ r hX hM hq hWM hr hZ hlo hhi P

/-- A union of shifted successes is transferred once, then union-bounded.
Thus the likelihood error is not multiplied by the number of slots. -/
theorem principal_microcell_uniform_cover_transfer {V : Type*} [Fintype V]
    (X W M q Q : ℕ) (p : ℤ) (r : Fin M)
    (hX : 0 < X) (hM : 0 < M) (hq : 0 < q) (hQ : 0 < Q) (hWM : W ∣ M)
    (hr : r.val.Coprime W) (hres : p % M = r.val) (hZ : 0 < harmonicNormalizer X W)
    (hlo : (X : ℤ) ≤ (p / (M*q : ℕ)) * (M*q : ℕ))
    (hhi : (p / (M*q : ℕ)) * (M*q : ℕ) + (M*q : ℕ) ≤ (X ^ 2 : ℕ))
    (P : V → ℤ → Prop)
    (hsmall : (M*q : ℕ) / (X : ℝ) ≤ 1 / (4 * (Q : ℝ)))
    (hcover : 3 / (4 * (Q : ℝ)) ≤ event (uniformIntervalMass 0 q)
      (fun ell => ∃ v, P v (alignmentMicrocellFirst (M*q : ℕ) M p + M*ell))) :
    1 / (2 * (Q : ℝ)) ≤ ∑ v, event (conditionMass (integerMass X W)
      (fun z => principalMicrocellExposure (M*q) M z = principalMicrocellExposure (M*q) M p)) (P v) := by
  have he := principal_microcell_harmonic_event_error X W M q p r hX hM hq hWM hr hres hZ hlo hhi
    (fun z => ∃ v, P v z)
  have hh := (abs_le.mp (he.trans hsmall)).1
  have hu := event_union_bound (conditionMass (integerMass X W)
    (fun z => principalMicrocellExposure (M*q) M z = principalMicrocellExposure (M*q) M p))
    Finset.univ P (conditionMass_nonneg _ _ (integerMass_nonneg hZ))
  simp only [Finset.mem_univ, true_and] at hu
  have hQ' : (Q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hQ)
  have heq : (3 : ℝ)/(4*Q) - 1/(4*Q) = 1/(2*Q) := by field_simp; ring
  linarith
end Hindman168
