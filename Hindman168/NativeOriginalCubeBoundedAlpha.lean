import Hindman168.NativeOriginalCubeAlphaBoxes
import Hindman168.ComplexMeanIntegralScaling
import Hindman168.BoundedLipschitzNormalization

/-! Uniform explicit alpha-box laws for arbitrary fixed norm/Lipschitz budgets. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeCubeBoundedAlphaHaarLaw {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) : Prop :=
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta c C : ℝ, 0 < c → 0 ≤ C → ∀ B : ℝ, 0 ≤ B → ∀ T : NNReal, ∀ ε : ℝ, 0 < ε →
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 < α → α < α0 →
      ∀ t : ℕ, 0 < t → (M : ℤ) ∣ (t : ℤ) →
      ∀ᶠ m in atTop, ∀ q : Fin (s+2), ∀ lo hi : Fin (q.val+1) → ℝ, ∀ v : Fin (q.val+1) → ℤ,
        (∀ i : Fin q.val, (M : ℤ) ∣ v i.succ) →
        (∀ j, c*α*L m ≤ hi j-lo j ∧ hi j-lo j ≤ C*α*L m) →
        (|lo 0-beta*L m| ≤ C*α*L m ∧ |hi 0-beta*L m| ≤ C*α*L m) →
        (∀ i : Fin q.val, |lo i.succ| ≤ C*α*L m ∧ |hi i.succ| ≤ C*α*L m) →
        ∀ f : C((Finset (Fin q.val) → D.G ⧸ D.Γ), ℂ), LipschitzWith T f → (∀ y, ‖f y‖ ≤ B) →
          ‖finiteComplexSetMean (alignmentBoxClass (fun j => ⌈lo j⌉) (fun j => ⌈hi j⌉) v t)
            (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) -
            ∫ y, f y ∂nativeResidueCubeHaarImage D H
              (sigma (signedPeriodResidue M hM (v 0))) (hRat _)
              q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)‖ < ε

theorem native_cube_alpha_bounded_tests {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G)
    (hlaw : NativeCubeAlphaHaarLaw D H L P M hM sigma hRat h) :
    NativeCubeBoundedAlphaHaarLaw D H L P M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta c C hc hC B hB T ε hε
  let R : ℝ := 1+B+(T : ℝ)
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨α0,hα0,ha⟩ := hlaw beta c C hc hC (ε/R) (div_pos hε hR)
  refine ⟨α0,hα0,?_⟩
  intro α hα hα' t ht hMt
  filter_upwards [ha α hα hα' t ht hMt] with m hm
  intro q lo hi v hv hlen hbase hinc f hf hnorm
  have hBR : B ≤ R := by dsimp only [R]; linarith [T.coe_nonneg]
  have hTR : (T : ℝ) ≤ R := by dsimp only [R]; linarith
  have hunit := bounded_lipschitz_normalization (Finset (Fin q.val) → D.G ⧸ D.Γ)
    f B (T : ℝ) R hR hBR hTR hnorm (by simpa only [Real.toNNReal_coe] using hf)
  have hg := hm q lo hi v hv hlen hbase hinc ((R : ℂ)⁻¹ • f) hunit
  simp only [ContinuousMap.smul_apply] at hg
  rw [complex_mean_integral_normalization_norm _ _ _ _ R hR] at hg
  have hh := mul_lt_mul_of_pos_left hg hR
  simpa only [← mul_assoc,mul_inv_cancel₀ hR.ne',one_mul,mul_div_cancel₀ _ hR.ne'] using hh

end Hindman168
