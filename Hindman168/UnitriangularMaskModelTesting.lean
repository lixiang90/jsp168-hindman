import Hindman168.UnitriangularCubeGeometry
import Hindman168.NilNaturalQuotientTesting

/-! The retained model-error nilsequence detector instantiated in the actual
unitriangular integer coset space. No compactness, lattice discreteness,
quotient metric or group nilpotency assumption is supplied by the caller.
The original arithmetic order, weight and dual-control requirements remain. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical

 theorem unitriangular_maskModel_testing_uniform {a m N : ℕ}
    (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (col : Fin (m+1))
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C ((a - 1) + 1) ρ model col)
    (H : Set C(Unitriangular a ℝ ⧸ integerUnitriangularLattice a, ℝ))
    (hH : IsCompact H) (B : ℝ) (hB0 : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ t : PieceLinearNilTest (integerUnitriangularLattice a),
      (∀ p, t.obs p ∈ H) → (∀ p z, |t.obs p z| ≤ B) →
      |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) *
          piecewiseLinearNilsequence (integerUnitriangularLattice a) (maskGeneratedMaster m gap)
            gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  letI := unitriangular_locallyCompact (n := a)
  letI := integerUnitriangularLattice_discrete (n := a)
  letI := integerUnitriangularLattice_quotient_compact (n := a)
  exact nilNaturalQuotient_maskModel_testing_uniform (integerUnitriangularLattice a)
    unitriangular_nilpotencyClass_le
    (fun i _ => unitriangular_nilClosedLowerCentral_layer_quotient_compact i)
    gap C hC col hgap htail ρ model hm hρ hdual H hH B hB0

end Hindman168
