import Hindman168.NilLowerCentralGeometry
import Hindman168.MaskNilsequenceTesting

/-! Original-law nilsequence testing with the actual lower central series.
The filtration axioms and terminal layer are proved, and the remaining
lattice cocompactness input is needed only at the finitely many layers <=s.
The quotient metric topology and continuous quotient map are explicit. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [WeaklyLocallyCompactSpace G] [T2Space G] [Group.IsNilpotent G]

section MetricQuotient
variable (Γ : Subgroup G) [qMetric : MetricSpace (G ⧸ Γ)]
local instance lowerCentralMetricQuotientTopology : TopologicalSpace (G ⧸ Γ) :=
  qMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable [CompactSpace (G ⧸ Γ)]

theorem nilLowerCentral_original_nilsequence_testing_uniform {s n N m : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hπ : Continuous ((↑) : G → G ⧸ Γ))
    (hclosed : ∀ i, i ≤ s → IsClosed (nilLowerCentralFiltration G i : Set G))
    (hquot : ∀ i, i ≤ s → CompactSpace ((nilLowerCentralFiltration G i) ⧸
      filtrationLayerLattice (nilLowerCentralFiltration G) Γ i))
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
    (B : ℝ) (hB0 : 0 ≤ B) (Lip : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      t.Admissible B Lip →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence Γ F gap (fun _ => t.obs)
          (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  have hq := nilLowerCentral_finite_layer_quotients hs Γ hquot
  have hc := nilLowerCentral_cube_compact_from_layer_quotients (d := s+1) Γ hπ
    (nilLowerCentral_finite_closed_layers hs hclosed) hq
  exact upperFaceCubeGroup_original_nilsequence_testing_uniform (Nat.succ_pos s)
    (nilLowerCentralFiltration G) nilLowerCentralFiltration_conditions (nilLowerCentralFiltration_terminal hs) nilLowerCentralFiltration_zero nilLowerCentralFiltration_one Γ hc
    hF C hN label gap horder htail e he hdual B hB0 Lip

theorem nilClosedLowerCentral_original_nilsequence_testing_uniform {s n N m : ℕ} (hs : Group.nilpotencyClass G ≤ s)
    (hπ : Continuous ((↑) : G → G ⧸ Γ))
    
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
    (B : ℝ) (hB0 : 0 ≤ B) (Lip : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      t.Admissible B Lip →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence Γ F gap (fun _ => t.obs)
          (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  have hq := nilClosedLowerCentral_finite_layer_quotients hs Γ hquot
  have hc := nilClosedLowerCentral_cube_compact_from_layer_quotients (d := s+1) Γ hπ  hq
  exact upperFaceCubeGroup_original_nilsequence_testing_uniform (Nat.succ_pos s)
    (nilClosedLowerCentralFiltration G) nilClosedLowerCentralFiltration_conditions (nilClosedLowerCentralFiltration_terminal hs) nilClosedLowerCentralFiltration_zero nilClosedLowerCentralFiltration_one Γ hc
    hF C hN label gap horder htail e he hdual B hB0 Lip

theorem nilClosedLowerCentral_maskModel_testing_uniform {s m N : ℕ}
    (hs : Group.nilpotencyClass G ≤ s) (hπ : Continuous ((↑) : G → G ⧸ Γ))
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
    (B : ℝ) (hB0 : 0 ≤ B) (Lip : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      t.Admissible B Lip →
      |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) * piecewiseLinearNilsequence Γ (maskGeneratedMaster m gap)
          gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  have he : ∀ᶠ w in atTop, ∀ y, |ρ w y - model w y| ≤
      1 + masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y :=
    hρ.mono (fun w hw y => model_error_abs_bound (hw y) (hm w y))
  exact nilClosedLowerCentral_original_nilsequence_testing_uniform Γ hs hπ hquot
    hF C hC (fun _ => col) gap hgap htail (fun w y => ρ w y - model w y) he
    (maskBlockModelDualControl_zeroPrime gap C (s+1) ρ model col hdual) B hB0 Lip

end MetricQuotient
end Hindman168
