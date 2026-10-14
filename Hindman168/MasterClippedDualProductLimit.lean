import Hindman168.MasterMixedDualClipping
import Hindman168.FiniteCenteredLimitTransfer

/-!
# Actual clipped mixed dual products retain the centered root limit

The original product limit and every weighted clipping input are derived
under one fixed master. Distinct replica dimensions, prime arities, local
denominators and finite varying J choices are retained, including b=0.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.normalized_clipped_dual_product_tendsto {n r N m b d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (dim arity : Fin b → ℕ) (hd : ∀ q, dim q ≤ d) (hpos : ∀ q, 0 < dim q)
    (e : (Σ q, Fin (arity q)) ≃ Fin r)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (gap : ℕ → Fin b → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap w q).val)
    (hgap : ∀ᶠ w in atTop, ∀ q, (gap w q).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ a, 1 ≤ J a) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ) (hden : ∀ q, den q ∈ tests q)
    (masterSlot : ∀ q, Fin (arity q) → Fin n) (hmasterSlot : ∀ q, Function.Injective (masterSlot q))
    (hinclude : ∀ q f, f ∈ tests q → MvPolynomial.rename (masterSlot q) f ∈ D)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (hε : ∀ᶠ w in atTop, ∀ q x, |ε w q x| ≤ 1)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ)
    (hg : ∀ᶠ w in atTop, ∀ q x S y, |g w q x S y| ≤ 1 + masterPredictionBlockMask F C label w y) 
    (cut : Fin b → ℝ) (hcut : ∀ q, predictionDualThreshold (dim q) < cut q) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (masterPredictionBlockMask F C label w y - 1) *
        ∏ q, predictionClip (cut q)
          (masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y)))
      atTop (𝓝 0) := by
  have horig := hF.normalized_dual_product_all_b_tendsto hD dim arity hd hpos e C hN label
    tail htail root gap htailroot htailgap hgap J hJ choice tests den hden masterSlot
    hmasterSlot hinclude ε hε g hg
  have herr := hF.normalized_mixed_dual_clipping_tendsto hD dim arity C hN label tail htail
    root gap htailroot htailgap J hJ choice tests den hden masterSlot hmasterSlot hinclude
    ε hε g hg cut hcut
  have hμ : ∀ᶠ w in atTop, ∀ y, 0 ≤ integerMass (F.cutoff w (root w).val) (primorial w) y :=
    hF.raw_cutoffs_valid.mono (fun w hw => integerMass_nonneg
      (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
  have hc : ∀ᶠ w in atTop, ∀ y, |masterPredictionBlockMask F C label w y - 1| ≤
      1 + masterPredictionBlockMask F C label w y :=
    (hF.block_mask_eventually_nonneg C hN label).mono
      (fun _ hw y => centered_mask_abs_le_one_add (hw y))
  exact weighted_centered_limit_transfer
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => masterPredictionBlockMask F C label w y - 1)
    (fun w y => 1 + masterPredictionBlockMask F C label w y)
    (fun w y => ∏ q, masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y)
    (fun w y => ∏ q, predictionClip (cut q)
      (masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y)) hμ hc herr horig

end Hindman168
