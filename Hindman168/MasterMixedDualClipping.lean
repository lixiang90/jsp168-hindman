import Hindman168.MasterDualWeightedLaw
import Hindman168.PredictionProductClipping

/-!
# Actual mixed local dual products have vanishing weighted clipping error

Every factor retains its own dimension, prime arity, denominator and gap.
The moment, clipping and root-mass inputs are derived under the same fixed
master family. No product-moment or clipping-limit premise is supplied.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.normalized_mixed_dual_clipping_tendsto {n N m b K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (dim arity : Fin b → ℕ)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (gap : ℕ → Fin b → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap w q).val)
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
      (fun y => (1 + masterPredictionBlockMask F C label w y) *
        |(∏ q, masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y) -
          ∏ q, predictionClip (cut q)
            (masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y)|))
      atTop (𝓝 0) := by
  let μ w := integerMass (F.cutoff w (root w).val) (primorial w)
  let H w y := 1 + masterPredictionBlockMask F C label w y
  let f q w y := masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y
  have hμ : ∀ᶠ w in atTop, ∀ y, 0 ≤ μ w y :=
    hF.raw_cutoffs_valid.mono (fun w hw => integerMass_nonneg
      (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
  have hH : ∀ᶠ w in atTop, ∀ y, 0 ≤ H w y :=
    (hF.block_mask_eventually_nonneg C hN label).mono
      (fun _ hw y => add_nonneg zero_le_one (hw y))
  have hbase : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in atTop, expectation (μ w) (H w) ≤ B :=
    ⟨3, by norm_num, hF.dual_weighted_root_mass_eventually_le C hN label tail htail root htailroot⟩
  have hf (q : Fin b) : WeightedMomentBounded μ H (f q) := by
    have heq : f q = masterSingleGoodDualTest F (dim q) (fun w => gap w q) J
        (fun w => choice w q) (tests q) (den q) (fun w => ε w q) (fun w => g w q) := by
      funext w y
      exact master_replica_good_dual_single F dim arity gap J choice tests den ε g w q y
    rw [heq]
    exact hF.single_dual_weighted_moments_bounded hD C hN label tail htail root
      (fun w => gap w q) htailroot (htailgap.mono (fun _ hw => hw q)) J hJ
      (fun w => choice w q) (tests q) (den q) (hden q) (masterSlot q) (hmasterSlot q)
      (hinclude q) (fun w => ε w q) (hε.mono (fun _ hw => hw q))
      (fun w => g w q) (hg.mono (fun _ hw => hw q))
  have hclip (q : Fin b) : Tendsto (fun w => expectation (μ w)
      (fun y => H w y * |f q w y - predictionClip (cut q) (f q w y)| ^ 2)) atTop (𝓝 0) := by
    have heq : f q = masterSingleGoodDualTest F (dim q) (fun w => gap w q) J
        (fun w => choice w q) (tests q) (den q) (fun w => ε w q) (fun w => g w q) := by
      funext w y
      exact master_replica_good_dual_single F dim arity gap J choice tests den ε g w q y
    rw [heq]
    exact hF.normalized_single_dual_clipping_tendsto hD C hN label tail htail root
      (fun w => gap w q) htailroot (htailgap.mono (fun _ hw => hw q)) J hJ
      (fun w => choice w q) (tests q) (den q) (hden q) (masterSlot q) (hmasterSlot q)
      (hinclude q) (fun w => ε w q) (hε.mono (fun _ hw => hw q))
      (fun w => g w q) (hg.mono (fun _ hw => hw q)) (cut q) (hcut q) 2 (by norm_num)
  have hc (q : Fin b) : 0 ≤ cut q :=
    (zero_le_one.trans (predictionDualThreshold_ge_one (dim q))).trans (hcut q).le
  exact prediction_product_clipping_error_tendsto μ H f cut hμ hH hbase hf hc hclip Finset.univ

end Hindman168
