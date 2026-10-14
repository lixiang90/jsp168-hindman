import Hindman168.MaskNilsequenceTesting

/-! One finite family of the already constructed block models retains
count replacement, target cube cancellation, companion diagonalization
and full dual prefixes, and simultaneously tests every allowed nilorbit. -/

namespace Hindman168
open Filter FiniteMass NNReal
open MaskOriginalSampling
open scoped Topology Classical

theorem maskGenerated_finite_models_counting_and_nilsequence_testing
    {G : Type*} [Group G] {m N : ℕ} {ι : Type*} [Fintype ι]
    (gap : ℕ → Fin N) (C : ℕ → Chain (m+1)) (d : ℕ) (hd : 0 < d)
    (fil : ℕ → Subgroup G) (hfil : CubeGroupFiltration fil)
    (htop : fil d = ⊥) (hzero : fil 0 = ⊤) (hone : fil 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup fil d)))
    (coeff : ι → Fin (m+1) → ℚ) (hcoeff : ∀ i col, 0 < coeff i col)
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ : ι → Fin (m+1) → ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ i col y, 0 ≤ ρ i col w y ∧
      ρ i col w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ι → Fin (m+1) → ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ i col w y, 0 ≤ model i col w y ∧ model i col w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      (∀ i col, maskBlockModelDualControl gap C d (ρ i col) (model i col) col) ∧
      (∀ i, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ J : ℕ, 0 < J →
        Tendsto (fun w => maskEndpointTargetCube gap C t J w
          (fun y => ρ i (targetRootAnchor gap t) w y - model i (targetRootAnchor gap t) w y)) atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ i,
        maskModelReplacementQuality gap (coeff i) C (ρ i) (model i) ε w) ∧
      (∀ᶠ w in atTop, ∀ i col, maskBlockModelDualPrefix gap C d (stage w) (ρ i col) (model i col) col w) ∧
      (∀ᶠ w in atTop, ∀ i, maskModelReplacementQuality gap (coeff i) C (ρ i) (model i)
        (1 / ((stage w : ℝ)+1)) w) ∧
      (∀ i col, ∀ B : ℝ, 0 ≤ B → ∀ Lip : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
        ∀ t : PieceLinearNilTest Γ, t.Admissible B Lip →
        |expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun y => (ρ i col w y - model i col w y) * piecewiseLinearNilsequence Γ
            (maskGeneratedMaster m gap) gap (fun _ => t.obs) (fun _ => t.g) (fun _ => t.x) w y)| < ε) := by
  obtain ⟨stage, model, hs, hsw, hm, hp, hdual, hcubes, hquality, hprefix, hstagequality⟩ :=
    maskGenerated_finite_model_replacement_family gap C d hd coeff hcoeff hC hgap htail ρ hρ P hP
  refine ⟨stage, model, hs, hsw, hm, hp, hdual, hcubes, hquality, hprefix, hstagequality, ?_⟩
  intro i col B hB Lip
  exact maskBlockModelDualControl_nilsequence_testing hd fil hfil htop hzero hone Γ hcompact gap C hC col
    (hgap.mono (fun _ hw => hw col)) (htail.mono (fun _ hw => hw col)) (ρ i col) (model i col)
    (hm i col) (hρ.mono (fun _ hw y => hw i col y)) (hdual i col) B hB Lip

end Hindman168
