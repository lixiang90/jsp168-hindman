import Hindman168.ProductCosetMetric
import Hindman168.PieceNilLipschitzComposition
import Mathlib.Analysis.Normed.Group.Uniform

/-! Addition of actual piecewise nilsequence representations uses the
original product group and the product of the two specified lattices.
Observable bounds and Lipschitz constants are explicitly additive. -/

namespace Hindman168
open NNReal

variable {G H : Type*} [Group G] [Group H] (Γ : Subgroup G) (Λ : Subgroup H)
  [MetricSpace (G ⧸ Γ)] [MetricSpace (H ⧸ Λ)]

noncomputable def productSumObservable (f : C(G ⧸ Γ, ℝ)) (g : C(H ⧸ Λ, ℝ)) :
    letI := productCosetMetric Γ Λ
    C((G × H) ⧸ Γ.prod Λ, ℝ) :=
  letI := productCosetMetric Γ Λ
  ⟨fun z => f (productCosetMap Γ Λ z).1 + g (productCosetMap Γ Λ z).2,
    ((f.continuous.comp continuous_fst).add (g.continuous.comp continuous_snd)).comp
      (productCosetIsometryEquiv Γ Λ).continuous⟩

theorem productSumObservable_lipschitz (f : C(G ⧸ Γ, ℝ)) (g : C(H ⧸ Λ, ℝ))
    {Lf Lg : ℝ≥0} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) :
    letI := productCosetMetric Γ Λ
    LipschitzWith (Lf + Lg) (productSumObservable Γ Λ f g) := by
  letI := productCosetMetric Γ Λ
  have hi := (productCosetIsometryEquiv Γ Λ).isometry.lipschitz
  have ha := hf.comp (LipschitzWith.prod_fst.comp hi)
  have hb := hg.comp (LipschitzWith.prod_snd.comp hi)
  change LipschitzWith (Lf + Lg) (fun z =>
    f ((productCosetIsometryEquiv Γ Λ) z).1 + g ((productCosetIsometryEquiv Γ Λ) z).2)
  simpa only [mul_one, Function.comp_def] using ha.add hb

theorem piecewiseLinearNilsequence_product_sum {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (obs₁ : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ))
    (obs₂ : ℕ → (ℤ × ℤ) → C(H ⧸ Λ, ℝ))
    (g₁ x₁ : ℕ → (ℤ × ℤ) → G) (g₂ x₂ : ℕ → (ℤ × ℤ) → H) (w : ℕ) (y : ℤ) :
    letI := productCosetMetric Γ Λ
    piecewiseLinearNilsequence (Γ.prod Λ) F gap
      (fun w p => productSumObservable Γ Λ (obs₁ w p) (obs₂ w p))
      (fun w p => (g₁ w p, g₂ w p)) (fun w p => (x₁ w p, x₂ w p)) w y =
      piecewiseLinearNilsequence Γ F gap obs₁ g₁ x₁ w y +
        piecewiseLinearNilsequence Λ F gap obs₂ g₂ x₂ w y := by
  letI := productCosetMetric Γ Λ
  simp [piecewiseLinearNilsequence, pieceLinearOrbit, productSumObservable, productCosetMap_mk]

theorem boundedPieceNilsequence_add_product {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (f g : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F gap f) (hg : IsBoundedPieceNilsequence Λ F gap g) :
    letI := productCosetMetric Γ Λ
    IsBoundedPieceNilsequence (Γ.prod Λ) F gap (fun w y => f w y + g w y) := by
  letI := productCosetMetric Γ Λ
  obtain ⟨obs₁, g₁, x₁, B₁, L₁, hB₁, hb₁, hl₁, rfl⟩ := hf
  obtain ⟨obs₂, g₂, x₂, B₂, L₂, hB₂, hb₂, hl₂, rfl⟩ := hg
  refine ⟨fun w p => productSumObservable Γ Λ (obs₁ w p) (obs₂ w p),
    fun w p => (g₁ w p, g₂ w p), fun w p => (x₁ w p, x₂ w p),
    B₁ + B₂, L₁ + L₂, add_nonneg hB₁ hB₂, ?_, ?_, ?_⟩
  · intro w p z
    exact (abs_add_le _ _).trans (add_le_add (hb₁ w p _) (hb₂ w p _))
  · exact fun w p => productSumObservable_lipschitz Γ Λ _ _ (hl₁ w p) (hl₂ w p)
  · funext w y
    exact (piecewiseLinearNilsequence_product_sum Γ Λ F gap obs₁ obs₂ g₁ x₁ g₂ x₂ w y).symm

omit [Group H] [MetricSpace (H ⧸ Λ)] in
theorem boundedPieceNilsequence_smul {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (f : ℕ → ℤ → ℝ) (hf : IsBoundedPieceNilsequence Γ F gap f) (r : ℝ) :
    IsBoundedPieceNilsequence Γ F gap (fun w y => r * f w y) := by
  apply boundedPieceNilsequence_lipschitz_comp Γ F gap f hf (fun t => r * t) ‖r‖₊
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |r * x - r * y| ≤ ‖r‖ * |x - y|
  simp only [← mul_sub, abs_mul, Real.norm_eq_abs, le_refl]

end Hindman168
