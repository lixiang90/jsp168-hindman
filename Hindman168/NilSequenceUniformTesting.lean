import Hindman168.NilSequenceTestingLimit

/-! Uniform original-law testing follows from testing every admissible
stage-varying family. The maximizing choice uses no extra analytic bound. -/

namespace Hindman168
open Filter FiniteMass NNReal
open scoped Topology Classical

theorem uniform_abs_small_of_all_admissible_sequences {X : Type*}
    (Q : ℕ → X → Prop) (hQ : ∀ w, ∃ x, Q w x) (f : ℕ → X → ℝ)
    (hf : ∀ x : ℕ → X, (∀ w, Q w (x w)) → Tendsto (fun w => f w (x w)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ x, Q w x → |f w x| < ε := by
  intro ε hε
  have hc (w : ℕ) : ∃ x, Q w x ∧ ((∃ y, Q w y ∧ ε ≤ |f w y|) → ε ≤ |f w x|) := by
    by_cases h : ∃ y, Q w y ∧ ε ≤ |f w y|
    · obtain ⟨x, hx, hbad⟩ := h
      exact ⟨x, hx, fun _ => hbad⟩
    · obtain ⟨x, hx⟩ := hQ w
      exact ⟨x, hx, fun hy => False.elim (h hy)⟩
  choose x hx hmax using hc
  have hs := (hf x hx).abs.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hε))
  filter_upwards [hs] with w hw
  intro y hy
  by_contra hbad
  have hle : ε ≤ |f w y| := le_of_not_gt hbad
  exact (not_le_of_gt (by simpa only [abs_zero] using hw)) (hmax w ⟨y, hy, hle⟩)

structure PieceLinearNilTest {G : Type*} [Group G] (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] where
  obs : (ℤ × ℤ) → C(G ⧸ Γ, ℝ)
  g : (ℤ × ℤ) → G
  x : (ℤ × ℤ) → G

noncomputable def PieceLinearNilTest.Admissible {G : Type*} [Group G]
    {Γ : Subgroup G} [MetricSpace (G ⧸ Γ)] (t : PieceLinearNilTest Γ) (B : ℝ) (Lip : ℝ≥0) : Prop :=
  (∀ p z, |t.obs p z| ≤ B) ∧ (∀ p, LipschitzWith Lip (t.obs p))

theorem upperFaceCubeGroup_original_nilsequence_testing_uniform
    {G : Type*} [Group G] {d n N m : ℕ} (hd : 0 < d)
    (fil : ℕ → Subgroup G) (hfil : CubeGroupFiltration fil)
    (htop : fil d = ⊥) (hzero : fil 0 = ⊤) (hone : fil 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup fil d)))
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (gap : ℕ → Fin N)
    (horder : ∀ᶠ w in atTop, (gap w).val ≤ (C w).pivot (label w))
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ Finset.range (gap w).val)
    (e : ℕ → ℤ → ℝ)
    (he : ∀ᶠ w in atTop, ∀ y, |e w y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (hdual : ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput 0 d, u.Admissible F C label w →
        |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
          (fun y => e w y * (originalZeroPrimeTemplate (n := n) d gap (fun _ => (0 : Fin 1))).dual
            F (fun _ => J) u w y)| < η)
    (B : ℝ) (hB0 : 0 ≤ B) (Lip : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ t : PieceLinearNilTest Γ,
      t.Admissible B Lip →
      |expectation (integerMass (F.cutoff w ((C w).pivot (label w))) (primorial w))
        (fun y => e w y * piecewiseLinearNilsequence Γ F gap (fun _ => t.obs)
          (fun _ => t.g) (fun _ => t.x) w y)| < ε := by
  let Q (_ : ℕ) (t : PieceLinearNilTest Γ) := t.Admissible B Lip
  have hQ (w : ℕ) : ∃ t, Q w t := by
    refine ⟨⟨fun _ => 0, fun _ => 1, fun _ => 1⟩, ?_⟩
    exact ⟨fun _ _ => by simpa using hB0, fun _ => (LipschitzWith.const 0).weaken (by positivity)⟩
  apply uniform_abs_small_of_all_admissible_sequences Q hQ
  intro t ht
  exact upperFaceCubeGroup_original_nilsequence_testing hd fil hfil htop hzero hone Γ hcompact
    hF C hN label gap horder htail e he hdual (fun w => (t w).obs) (fun w => (t w).g)
    (fun w => (t w).x) B hB0 Lip (fun w => (ht w).1) (fun w => (ht w).2)

end Hindman168
