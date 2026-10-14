import Hindman168.NativeLowerCentralCubeGeometry
import Hindman168.NilNaturalQuotientTesting

/-! Original-law model-error testing on arbitrary native nilmanifolds.
Layer cocompactness is proved above, not supplied by the caller. The
arithmetic order, weight, compact observable and dual-control premises
are exactly the retained analytic interface. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsTopologicalGroup G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three
include I

theorem native_maskModel_testing_uniform
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] {m N : ℕ}
    (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (col : Fin (m + 1))
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C (Group.nilpotencyClass G + 1) ρ model col)
    (obs : Set C(G ⧸ Γ, ℝ)) (hobs : IsCompact obs) (B : ℝ) (hB0 : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
      ∀ t : PieceLinearNilTest Γ,
      (∀ p, t.obs p ∈ obs) → (∀ p z, |t.obs p z| ≤ B) →
      |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) *
          piecewiseLinearNilsequence Γ (maskGeneratedMaster m gap)
            gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  letI := nativeLieGroup_locallyCompact (E := E) (I := I) (G := G)
  exact nilNaturalQuotient_maskModel_testing_uniform Γ le_rfl
    (fun i _ => native_nilClosedLowerCentral_layer_quotient_compact (E := E) (I := I) Γ i)
    gap C hC col hgap htail ρ model hm hρ hdual obs hobs B hB0

end Hindman168
