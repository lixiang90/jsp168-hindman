import Hindman168.NilSequenceUniformTesting
import Hindman168.MaskFiniteModelReplacementFamily

/-! The existing simultaneous mask/counting models also pass the paper's
piecewise nilsequence tests. The model is retained, not reconstructed. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical

theorem maskGeneratedDualTemplates_zero {m N : ℕ} (gap : ℕ → Fin N)
    (d : ℕ) (gap₀ : ℕ → Fin N) :
    maskGeneratedDualTemplates m gap d gap₀ 0 =
      originalZeroPrimeTemplate (n := maskMasterArity m) d gap₀ (fun _ => (0 : Fin 1)) := rfl

theorem maskBlockModelDualControl_zeroPrime {m N : ℕ} (gap : ℕ → Fin N)
    (C : ℕ → Chain (m+1)) (d : ℕ) (ρ model : ℕ → ℤ → ℝ) (col : Fin (m+1))
    (hdual : maskBlockModelDualControl gap C d ρ model col) :
    ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 d,
        u.Admissible (maskGeneratedMaster m gap) C (fun _ => col) w →
        |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun y => (ρ w y - model w y) *
            (originalZeroPrimeTemplate (n := maskMasterArity m) d gap (fun _ => (0 : Fin 1))).dual
              (maskGeneratedMaster m gap) (fun _ => J) u w y)| < η := by
  exact hdual 0

theorem maskBlockModelDualControl_nilsequence_testing {G : Type*} [Group G]
    {m N d : ℕ} (hd : 0 < d) (fil : ℕ → Subgroup G) (hfil : CubeGroupFiltration fil)
    (htop : fil d = ⊥) (hzero : fil 0 = ⊤) (hone : fil 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup fil d)))
    (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) (col : Fin (m+1))
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C d ρ model col)
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
  exact upperFaceCubeGroup_original_nilsequence_testing_uniform hd fil hfil htop hzero hone Γ hcompact
    hF C hC (fun _ => col) gap hgap htail (fun w y => ρ w y - model w y) he
    (maskBlockModelDualControl_zeroPrime gap C d ρ model col hdual) B hB0 Lip

end Hindman168
