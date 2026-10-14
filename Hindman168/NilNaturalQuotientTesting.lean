import Hindman168.NilNaturalCosetMetric
import Hindman168.NilObservableCompactHulls
import Hindman168.NilCompactObservableTesting
import Hindman168.NilLowerCentralGeometry
import Hindman168.MaskNilsequenceTesting

/-! Canonical natural-quotient testing for an actual discrete lattice.
No auxiliary quotient metric or assumed continuous projection is needed.
For supplied compatible metrics the original distance/Lipschitz class is
retained by taking its compact hull in the natural function-space topology.
Finite rational-layer cocompactness remains explicit. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [WeaklyLocallyCompactSpace G] [Group.IsNilpotent G]
variable (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)]

theorem nilNaturalQuotient_compactObservable_testing_uniform {s n N m : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hquot : ∀ i, i ≤ s → CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i))
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (gap : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val)
    (e : ℕ → ℤ → ℝ)
    (he : ∀ᶠ w in atTop, ∀ y, |e w y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (hdual : ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 (s+1), u.Admissible F C label w →
        |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
          (fun y => e w y * (originalZeroPrimeTemplate (n := n) (s+1) gap (fun _ => (0 : Fin 1))).dual
            F (fun _ => J) u w y)| < η)
    (H : Set C(G ⧸ Γ, ℝ)) (hH : IsCompact H) (B : ℝ) (hB0 : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      (∀ p, t.obs p ∈ H) → (∀ p z, |t.obs p z| ≤ B) →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence Γ F gap (fun _ => t.obs)
          (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  have hq := nilClosedLowerCentral_finite_layer_quotients hs Γ hquot
  have hc := nilClosedLowerCentral_cube_compact_from_layer_quotients (d := s+1) Γ
    QuotientGroup.continuous_mk hq
  exact upperFaceCubeGroup_original_compactObservable_testing_uniform (Nat.succ_pos s)
    (nilClosedLowerCentralFiltration G) nilClosedLowerCentralFiltration_conditions
    (nilClosedLowerCentralFiltration_terminal hs) nilClosedLowerCentralFiltration_zero
    nilClosedLowerCentralFiltration_one Γ hc hF C hN label gap horder htail e he hdual H hH B hB0

theorem nilNaturalQuotient_originalMetric_testing_uniform {s n N m : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hquot : ∀ i, i ≤ s → CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i))
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (gap : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val)
    (e : ℕ → ℤ → ℝ)
    (he : ∀ᶠ w in atTop, ∀ y, |e w y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (hdual : ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 (s+1), u.Admissible F C label w →
        |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
          (fun y => e w y * (originalZeroPrimeTemplate (n := n) (s+1) gap (fun _ => (0 : Fin 1))).dual
            F (fun _ => J) u w y)| < η)
    (M : MetricSpace (G ⧸ Γ))
    (hM : QuotientGroup.instTopologicalSpace Γ = M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (hB0 : 0 ≤ B) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ z, |f z| ≤ B)
    (hL : ∀ f ∈ A, ∀ z z', dist (f z) (f z') ≤ (L : ℝ) * @dist (G ⧸ Γ) M.toDist z z') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      (∀ p, t.obs p ∈ A) →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence Γ F gap (fun _ => t.obs)
          (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  obtain ⟨H, hH, hAH⟩ := compatibleMetric_boundedLipschitz_compact_hull M hM A B L hB hL
  intro ε hε
  filter_upwards [nilNaturalQuotient_compactObservable_testing_uniform Γ hs hquot
    hF C hN label gap horder htail e he hdual H hH B hB0 ε hε] with w hw
  intro t ht
  exact hw t (fun p => hAH (ht p)) (fun p z => hB _ (ht p) z)

theorem nilNaturalQuotient_maskModel_testing_uniform {s m N : ℕ}
    (hs : Group.nilpotencyClass G ≤ s)
    (hquot : ∀ i, i ≤ s → CompactSpace ((nilClosedLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilClosedLowerCentralFiltration G) Γ i))
    (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (col : Fin (m+1))
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C (s+1) ρ model col)
    (H : Set C(G ⧸ Γ, ℝ)) (hH : IsCompact H) (B : ℝ) (hB0 : 0 ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      (∀ p, t.obs p ∈ H) → (∀ p z, |t.obs p z| ≤ B) →
      |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) * piecewiseLinearNilsequence Γ (maskGeneratedMaster m gap)
          gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have he : ∀ᶠ w in atTop, ∀ y, |ρ w y - model w y| ≤
      1 + masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y :=
    hρ.mono (fun w hw y => model_error_abs_bound (hw y) (hm w y))
  exact nilNaturalQuotient_compactObservable_testing_uniform Γ hs hquot hF C hC
    (fun _ => col) gap hgap htail (fun w y => ρ w y - model w y) he
    (maskBlockModelDualControl_zeroPrime gap C (s+1) ρ model col hdual) H hH B hB0

end Hindman168
