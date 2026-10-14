import Hindman168.NativeIndexedCellRecipeSynthesis
import Hindman168.NativeCellCorrelationTransfer

namespace Hindman168
open NNReal
open scoped Classical
universe u v

/-- The raw complex correlation delivered on K periods by an interval
inverse conclusion, with its actual native manifold and original bounds. -/
def HasNativePeriodCellCorrelator {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (M q K : ℕ) [NeZero q] (k : ℤ) (r : Fin M) (f : ℤ → ℝ)
    (γ : ℝ) (Lip : ℝ≥0) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (obs : C(D.G ⧸ D.Γ, ℂ)) (g x : D.G),
    (∀ z, ‖obs z‖ ≤ 1) ∧ LipschitzWith Lip obs ∧
    γ ≤ ‖finiteComplexMean (fun n : Fin (K * q) =>
      (f (k * (M * q : ℕ) + r.val + (M : ℤ) * (n.val : ZMod q).val) : ℂ) *
        obs (g ^ (n.val : ℤ) * x))‖

theorem native_period_cell_correlator_to_real {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (M q K : ℕ) [NeZero q] (hM : 0 < M) (hK : 0 < K)
    (k : ℤ) (r : Fin M) (f : ℤ → ℝ) (γ : ℝ) (Lip : ℝ≥0)
    (h : HasNativePeriodCellCorrelator D M q K k r f γ Lip) :
    HasNativeRealCellCorrelator D M q k r f γ Lip := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨obs, g, x, hb, hl, hc⟩ := h
  obtain ⟨_j, x', _η, obs', _hx, _hη, _he, hb', hl', hc'⟩ :=
    native_complete_cell_correlation_transfer D k M q K hM hK r f obs g x 1 Lip γ hb hl hc
  exact ⟨obs', g, x', hb', hl', hc'⟩

/-- From the fixed list of raw complex period correlators, construct
actual unit native real recipe families. Single-period extraction,
phase rotation and integer orbit rebasing preserve the correlation and
each listed manifold's fixed Lipschitz bound. -/
theorem native_indexed_period_cell_recipe_synthesis {s N : ℕ}
    {ι : Type v} (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (M q : ℕ → ℕ) [∀ w, NeZero (q w)]
    (K : ℕ) (hK : 0 < K) (A : Set ℕ)
    (hgeom : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧
      (F.modulus w : ℕ) = M w ∧ F.gap w (gap w).val = M w * q w)
    (C : (w : ℕ) → Finset (ℤ × Fin (M w))) (P : (w : ℕ) → C w → Prop)
    (f : ℕ → ℤ → ℝ) (γ : ℝ)
    (hlocal : ∀ w ∈ A, ∀ c : C w, P w c → ∃ i,
      HasNativePeriodCellCorrelator (D i) (M w) (q w) K c.val.1 c.val.2 (f w) γ (Lip i)) :
    ∃ recipes : ι → ℕ → ℤ → ℝ,
      (∀ i, nativePieceOn (D i) F gap (recipes i)) ∧
      (∀ i w y, |recipes i w y| ≤ 1) ∧
      (∀ w ∈ A, ∀ c : C w, P w c → ∃ i,
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            recipes i w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) := by
  apply native_indexed_real_cell_recipe_synthesis D Lip F gap M q A hgeom C P f γ
  intro w hw c hc
  obtain ⟨i, hi⟩ := hlocal w hw c hc
  exact ⟨i, native_period_cell_correlator_to_real (D i) (M w) (q w) K
    (hgeom w hw).1 hK c.val.1 c.val.2 (f w) γ (Lip i) hi⟩

end Hindman168
