import Hindman168.NativeLowerCentralCubeGeometry
import Hindman168.NativeNilmanifoldData
import Hindman168.MaskNilsequenceTesting

/-! Native-data testing in the specified compatible metric. The metric
topology is proved equal to the natural quotient topology; cube compactness
is transported through that equality, retaining the original metric and
its numerical Lipschitz constants. No layer compactness is assumed. -/

namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical Manifold ContDiff
universe u

theorem nativeNilmanifold_metric_topology {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    QuotientGroup.instTopologicalSpace D.Γ = D.metric.toUniformSpace.toTopologicalSpace := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact D.metric_quotientMap.isQuotientMap.isCoinducing.eq_coinduced.symm

theorem nativeNilmanifold_metric_cube_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) (d : ℕ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact (cosetCornerCubeSet D.Γ (upperFaceCubeGroup (nilClosedLowerCentralFiltration D.G) d)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  let P (t : TopologicalSpace (D.G ⧸ D.Γ)) :=
    @IsCompact (Option (ProperCubeVertex d) → D.G ⧸ D.Γ)
      (@Pi.topologicalSpace _ (fun _ => D.G ⧸ D.Γ) (fun _ => t))
      (cosetCornerCubeSet D.Γ (upperFaceCubeGroup (nilClosedLowerCentralFiltration D.G) d))
  have h : P (QuotientGroup.instTopologicalSpace D.Γ) :=
    native_nilClosedLowerCentral_cube_compact (E := D.E) (I := D.I) D.Γ d
  exact Eq.mp (congrArg P (nativeNilmanifold_metric_topology D)) h

theorem nativeMetric_maskModel_testing_uniform {s m N : ℕ}
    (D : NativeNilmanifoldData.{u} s) (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (col : Fin (m+1))
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤
      masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C (s+1) ρ model col) (B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest D.Γ,
      t.Admissible B Lip →
      |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) * piecewiseLinearNilsequence D.Γ (maskGeneratedMaster m gap)
          gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := by
    exact Eq.mp (congrArg (fun t => @CompactSpace (D.G ⧸ D.Γ) t)
      (nativeNilmanifold_metric_topology D)) D.quotientCompact
  exact maskBlockModelDualControl_nilsequence_testing (Nat.succ_pos s)
    (nilClosedLowerCentralFiltration D.G) nilClosedLowerCentralFiltration_conditions
    (nilClosedLowerCentralFiltration_terminal D.step_le) nilClosedLowerCentralFiltration_zero
    nilClosedLowerCentralFiltration_one D.Γ (nativeNilmanifold_metric_cube_compact D (s+1))
    gap C hC col hgap htail ρ model hm hρ hdual B hB Lip

theorem nativeMetric_original_zeroDual_testing_uniform {s b n N : ℕ}
    (D : NativeNilmanifoldData.{u} s)
    {A : Finset ℚ} {P : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A P F)
    (C : ℕ → Chain b) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (label : ℕ → Fin b) (gap : ℕ → Fin N)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val)
    (e : ℕ → ℤ → ℝ)
    (he : ∀ᶠ w in atTop, ∀ y, |e w y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (hdual : ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ v : OriginalSingleDualInput 0 (s+1), v.Admissible F C label w →
        |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
          (fun y => e w y * (originalZeroPrimeTemplate (n := n) (s+1) gap (fun _ => (0 : Fin 1))).dual
            F (fun _ => J) v w y)| < η)
    (B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest D.Γ,
      t.Admissible B Lip →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence D.Γ F gap
          (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := Eq.mp
    (congrArg (fun t => @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D))
    D.quotientCompact
  exact upperFaceCubeGroup_original_nilsequence_testing_uniform (Nat.succ_pos s)
    (nilClosedLowerCentralFiltration D.G) nilClosedLowerCentralFiltration_conditions
    (nilClosedLowerCentralFiltration_terminal D.step_le) nilClosedLowerCentralFiltration_zero
    nilClosedLowerCentralFiltration_one D.Γ (nativeNilmanifold_metric_cube_compact D (s+1))
    hF C hC label gap hgap htail e he hdual B hB Lip

end Hindman168
