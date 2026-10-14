import Hindman168.NativeLocalCellRecipeSynthesis

namespace Hindman168
open NNReal
open scoped Classical
universe u v

/-- Actual local real orbit data, with unit observable and specified
uniform Lipschitz bound, on the original complete-cell coordinates. -/
def HasNativeRealCellCorrelator {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (M q : ℕ) (k : ℤ) (r : Fin M) (f : ℤ → ℝ) (γ : ℝ) (Lip : ℝ≥0) : Prop :=
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∃ (obs : C(D.G ⧸ D.Γ, ℝ)) (g x : D.G),
    (∀ z, |obs z| ≤ 1) ∧ LipschitzWith Lip obs ∧
    γ ≤ finiteHaarMean (fun t : Fin q => f (completeResidueCellPoint k M q r t) *
      obs (pieceLinearOrbit D.Γ M (fun _ : Unit => g) (fun _ => x) ()
        (completeResidueCellPoint k M q r t)))

/-- Synthesize one native family on every listed manifold. Each family
uses only that manifold's actual local correlators. The list may be any
index type; subsequent assembly uses its finiteness. -/
theorem native_indexed_real_cell_recipe_synthesis {s N : ℕ}
    {ι : Type v} (D : ι → NativeNilmanifoldData.{u} s) (Lip : ι → ℝ≥0)
    (F : MasterParameterFamily) (gap : ℕ → Fin N) (M q : ℕ → ℕ) (A : Set ℕ)
    (hgeom : ∀ w ∈ A, 0 < M w ∧ 0 < q w ∧
      (F.modulus w : ℕ) = M w ∧ F.gap w (gap w).val = M w * q w)
    (C : (w : ℕ) → Finset (ℤ × Fin (M w))) (P : (w : ℕ) → C w → Prop)
    (f : ℕ → ℤ → ℝ) (γ : ℝ)
    (hlocal : ∀ w ∈ A, ∀ c : C w, P w c → ∃ i,
      HasNativeRealCellCorrelator (D i) (M w) (q w) c.val.1 c.val.2 (f w) γ (Lip i)) :
    ∃ recipes : ι → ℕ → ℤ → ℝ,
      (∀ i, nativePieceOn (D i) F gap (recipes i)) ∧
      (∀ i w y, |recipes i w y| ≤ 1) ∧
      (∀ w ∈ A, ∀ c : C w, P w c → ∃ i,
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            recipes i w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) := by
  have hsynth (i : ι) : ∃ recipe : ℕ → ℤ → ℝ,
      nativePieceOn (D i) F gap recipe ∧ (∀ w y, |recipe w y| ≤ 1) ∧
      (∀ w ∈ A, ∀ c : C w,
        HasNativeRealCellCorrelator (D i) (M w) (q w) c.val.1 c.val.2 (f w) γ (Lip i) →
        γ ≤ finiteHaarMean (fun t : Fin (q w) =>
          f w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t) *
            recipe w (completeResidueCellPoint c.val.1 (M w) (q w) c.val.2 t))) := by
    apply native_local_cell_recipe_synthesis (D i) F gap M q A hgeom C
      (fun w c => HasNativeRealCellCorrelator (D i) (M w) (q w) c.val.1 c.val.2 (f w) γ (Lip i))
      f γ (Lip i)
    intro w _ c hc
    exact hc
  choose recipes hr hb hgood using hsynth
  refine ⟨recipes, hr, hb, ?_⟩
  intro w hw c hc
  obtain ⟨i, hi⟩ := hlocal w hw c hc
  exact ⟨i, hgood i w hw c hi⟩

end Hindman168
