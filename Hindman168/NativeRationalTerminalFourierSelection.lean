import Hindman168.NativeRationalTerminalDiscrepancy

/-! Actual terminal FourierSelection for ANY original finite rational Lie filtration.
All original central/rational/lattice/action/canonical-Haar inputs are
PROVED using SAME actual terminal layer and SAME original specified metric. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff Classical
universe u

theorem native_rational_terminal_fourier_finite_selection {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ S : Finset (nativeRationalTerminalIndex D L → ℤ),
      ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ),
        ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f F‖ →
            ∃ k ∈ S, η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L k F)‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  obtain ⟨c, hc⟩ := native_rational_terminal_fourier_reconstruction D L (δ/8) (by positivity)
  let B : ℝ := 1 + ∑ k ∈ c.support, ‖c k‖
  let η : ℝ := min (δ/(4*B)) 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hbudget : (∑ k ∈ c.support, ‖c k‖) ≤ B := by
    dsimp only [B]
    linarith only []
  refine ⟨η, lt_min (by positivity) zero_lt_one, min_le_right _ _, c.support.image (fun k => -k), ?_⟩
  intro α a f F hF hlarge
  let P : C(D.G ⧸ D.Γ, ℂ) := c.sum (fun k z => z • nativeRationalTerminalFourierProjection D L (-k) F)
  have happrox : ‖F-P‖ < δ/8 := hc F hF
  have herror := native_nilmanifold_finite_discrepancy_norm D a f (F-P)
  have htriangle : ‖nativeNilmanifoldFiniteDiscrepancy D a f F‖ ≤
      ‖nativeNilmanifoldFiniteDiscrepancy D a f P‖ + 2*‖F-P‖ := by
    calc
      _ = ‖nativeNilmanifoldFiniteDiscrepancy D a f P +
          nativeNilmanifoldFiniteDiscrepancy D a f (F-P)‖ := by
        rw [map_sub]
        congr 1
        ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl herror)
  have hP : δ/2 ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f P‖ := by
    linarith only [hlarge, htriangle, happrox, hδ]
  have hex : ∃ k ∈ c.support,
      δ/(4*B) ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L (-k) F)‖ := by
    by_contra h
    push Not at h
    have he : nativeNilmanifoldFiniteDiscrepancy D a f P =
        ∑ k ∈ c.support, c k * nativeNilmanifoldFiniteDiscrepancy D a f
          (nativeRationalTerminalFourierProjection D L (-k) F) := by
      dsimp only [P]
      rw [Finsupp.sum, map_sum]
      simp only [map_smul, smul_eq_mul]
    have hb : ‖nativeNilmanifoldFiniteDiscrepancy D a f P‖ ≤ δ/4 := by
      rw [he]
      calc
        _ ≤ ∑ k ∈ c.support, ‖c k * nativeNilmanifoldFiniteDiscrepancy D a f
            (nativeRationalTerminalFourierProjection D L (-k) F)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ c.support, ‖c k‖*(δ/(4*B)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (h k hk).le (norm_nonneg _)
        _ = (∑ k ∈ c.support, ‖c k‖)*(δ/(4*B)) := by rw [Finset.sum_mul]
        _ ≤ B*(δ/(4*B)) := mul_le_mul_of_nonneg_right hbudget (by positivity)
        _ = δ/4 := by field_simp
    linarith only [hb, hP, hδ]
  obtain ⟨k, hk, hmean⟩ := hex
  exact ⟨-k, Finset.mem_image.mpr ⟨k, hk, rfl⟩, (min_le_left _ _).trans hmean⟩

theorem native_rational_terminal_fourier_bounded_alternative {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ M : ℕ, 0 < M ∧
      ∃ S : Finset (nativeRationalTerminalIndex D L → ℤ),
        (∀ k ∈ S, (∑ i, (k i).natAbs) ≤ M) ∧
        ∀ {α : Type*} (a : Finset α) (f : α → D.G ⧸ D.Γ),
          ∀ F ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
            δ ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f F‖ →
              η ≤ ‖nativeNilmanifoldFiniteDiscrepancy D a f (nativeRationalTerminalFourierProjection D L 0 F)‖ ∨
              ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖finiteComplexSetMean a
                (fun x => nativeRationalTerminalFourierProjection D L k F (f x))‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨η, hη, hη1, S, hS⟩ := native_rational_terminal_fourier_finite_selection D L δ hδ
  let M : ℕ := 1 + ∑ k ∈ S, ∑ i, (k i).natAbs
  refine ⟨η, hη, hη1, M, by dsimp only [M]; omega, S, ?_, ?_⟩
  · intro k hk
    have h := Finset.single_le_sum
      (f := fun j : nativeRationalTerminalIndex D L → ℤ => ∑ i, (j i).natAbs)
      (fun j _ => Nat.zero_le _) hk
    dsimp only [M]
    omega
  · intro α a f F hF hbad
    obtain ⟨k, hk, hlarge⟩ := hS a f F hF hbad
    by_cases h0 : k=0
    · exact Or.inl (h0 ▸ hlarge)
    · apply Or.inr
      refine ⟨k, hk, h0, ?_⟩
      rw [native_rational_finite_discrepancy_nonzero_terminal_projection D L a f k h0] at hlarge
      exact hlarge

end Hindman168
