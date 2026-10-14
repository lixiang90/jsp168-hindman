import Hindman168.ProductPieceNilRepresentation
import Hindman168.BoundedRealProductLipschitz

/-! Multiplication of original piecewise representations uses the SAME
product lattice as addition and keeps a uniform, explicit Lipschitz bound. -/

namespace Hindman168
open NNReal

variable {G H : Type*} [Group G] [Group H] (Γ : Subgroup G) (Λ : Subgroup H)
  [MetricSpace (G ⧸ Γ)] [MetricSpace (H ⧸ Λ)]

noncomputable def productMulObservable (f : C(G ⧸ Γ, ℝ)) (g : C(H ⧸ Λ, ℝ)) :
    letI := productCosetMetric Γ Λ
    C((G × H) ⧸ Γ.prod Λ, ℝ) :=
  letI := productCosetMetric Γ Λ
  ⟨fun z => f (productCosetMap Γ Λ z).1 * g (productCosetMap Γ Λ z).2,
    ((f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)).comp
      (productCosetIsometryEquiv Γ Λ).continuous⟩

theorem productMulObservable_lipschitz (f : C(G ⧸ Γ, ℝ)) (g : C(H ⧸ Λ, ℝ))
    {Lf Lg Bf Bg : ℝ≥0} (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hbf : ∀ z, |f z| ≤ Bf) (hbg : ∀ z, |g z| ≤ Bg) :
    letI := productCosetMetric Γ Λ
    LipschitzWith (Bf * Lg + Bg * Lf) (productMulObservable Γ Λ f g) := by
  letI := productCosetMetric Γ Λ
  have hi := (productCosetIsometryEquiv Γ Λ).isometry.lipschitz
  have ha : LipschitzWith Lf (fun z => f ((productCosetIsometryEquiv Γ Λ) z).1) := by
    simpa only [mul_one, Function.comp_def] using hf.comp (LipschitzWith.prod_fst.comp hi)
  have hb : LipschitzWith Lg (fun z => g ((productCosetIsometryEquiv Γ Λ) z).2) := by
    simpa only [mul_one, Function.comp_def] using hg.comp (LipschitzWith.prod_snd.comp hi)
  change LipschitzWith _ (fun z => f ((productCosetIsometryEquiv Γ Λ) z).1 *
    g ((productCosetIsometryEquiv Γ Λ) z).2)
  exact bounded_real_mul_lipschitz _ _ ha hb (fun z => hbf _) (fun z => hbg _)

theorem piecewiseLinearNilsequence_product_mul {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (obs₁ : ℕ → (ℤ × ℤ) → C(G ⧸ Γ, ℝ))
    (obs₂ : ℕ → (ℤ × ℤ) → C(H ⧸ Λ, ℝ))
    (g₁ x₁ : ℕ → (ℤ × ℤ) → G) (g₂ x₂ : ℕ → (ℤ × ℤ) → H) (w : ℕ) (y : ℤ) :
    letI := productCosetMetric Γ Λ
    piecewiseLinearNilsequence (Γ.prod Λ) F gap
      (fun w p => productMulObservable Γ Λ (obs₁ w p) (obs₂ w p))
      (fun w p => (g₁ w p, g₂ w p)) (fun w p => (x₁ w p, x₂ w p)) w y =
      piecewiseLinearNilsequence Γ F gap obs₁ g₁ x₁ w y *
        piecewiseLinearNilsequence Λ F gap obs₂ g₂ x₂ w y := by
  letI := productCosetMetric Γ Λ
  simp [piecewiseLinearNilsequence, pieceLinearOrbit, productMulObservable, productCosetMap_mk]

theorem boundedPieceNilsequence_mul_product {N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (f g : ℕ → ℤ → ℝ)
    (hf : IsBoundedPieceNilsequence Γ F gap f) (hg : IsBoundedPieceNilsequence Λ F gap g) :
    letI := productCosetMetric Γ Λ
    IsBoundedPieceNilsequence (Γ.prod Λ) F gap (fun w y => f w y * g w y) := by
  letI := productCosetMetric Γ Λ
  obtain ⟨obs₁, g₁, x₁, B₁, L₁, hB₁, hb₁, hl₁, rfl⟩ := hf
  obtain ⟨obs₂, g₂, x₂, B₂, L₂, hB₂, hb₂, hl₂, rfl⟩ := hg
  refine ⟨fun w p => productMulObservable Γ Λ (obs₁ w p) (obs₂ w p),
    fun w p => (g₁ w p, g₂ w p), fun w p => (x₁ w p, x₂ w p),
    B₁ * B₂, Real.toNNReal B₁ * L₂ + Real.toNNReal B₂ * L₁,
    mul_nonneg hB₁ hB₂, ?_, ?_, ?_⟩
  · intro w p z
    change |obs₁ w p _ * obs₂ w p _| ≤ B₁ * B₂
    rw [abs_mul]
    exact mul_le_mul (hb₁ w p _) (hb₂ w p _) (abs_nonneg _) hB₁
  · intro w p
    apply productMulObservable_lipschitz Γ Λ _ _ (hl₁ w p) (hl₂ w p)
    · simpa only [Real.coe_toNNReal _ hB₁] using hb₁ w p
    · simpa only [Real.coe_toNNReal _ hB₂] using hb₂ w p
  · funext w y
    exact (piecewiseLinearNilsequence_product_mul Γ Λ F gap obs₁ obs₂ g₁ x₁ g₂ x₂ w y).symm

end Hindman168
