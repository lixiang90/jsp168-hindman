import Hindman168.MasterDualClipping
import Hindman168.MasterFiniteDualTemplateLimit
import Hindman168.FiniteWeightedMomentProducts

/-!
# The actual unnormalized weighted root law and dual moment class

Its mass tends to two, derived from original mask mean one and harmonic
normalization. The bounded moment class of each actual local dual follows
from the proved all-fixed-order estimate with an explicit error one.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem master_replica_good_dual_single {N K b : ℕ} (F : MasterParameterFamily)
    (dim arity : Fin b → ℕ) (gap : ℕ → Fin b → Fin N)
    (J : Fin K → ℕ) (choice : ℕ → Fin b → Fin K)
    (tests : ∀ q, Finset (MvPolynomial (Fin (arity q)) ℤ))
    (den : ∀ q, MvPolynomial (Fin (arity q)) ℤ)
    (ε : ℕ → ∀ q, (Fin (arity q) → ℕ) → ℝ)
    (g : ℕ → ∀ q, (Fin (arity q) → ℕ) → CubeVertex (dim q) → ℤ → ℝ)
    (w : ℕ) (q : Fin b) (y : ℤ) :
    masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y =
      masterSingleGoodDualTest F (dim q) (fun w => gap w q) J (fun w => choice w q)
        (tests q) (den q) (fun w => ε w q) (fun w => g w q) w y := rfl

theorem MasterParameterConditions.dual_weighted_root_mass_tendsto
    {n N m : ℕ} {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => 1 + masterPredictionBlockMask F C label w y)) atTop (𝓝 2) := by
  have hm := hF.empty_dual_product_tendsto C hN label tail htail root htailroot
  have hs : Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => masterPredictionBlockMask F C label w y - 1) + 2) atTop (𝓝 2) := by
    simpa only [zero_add] using hm.add_const (2 : ℝ)
  apply hs.congr'
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  have ht := integerMass_total (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2
  rw [expectation_one_add, expectation_sub_one, ht]
  ring

theorem MasterParameterConditions.dual_weighted_root_mass_eventually_le
    {n N m : ℕ} {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A₀ D F)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val) :
    ∀ᶠ w in atTop, expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => 1 + masterPredictionBlockMask F C label w y) ≤ 3 :=
  (hF.dual_weighted_root_mass_tendsto C hN label tail htail root htailroot).eventually
    (Iio_mem_nhds (by norm_num : (2 : ℝ) < 3)) |>.mono (fun _ hw => hw.le)

theorem MasterParameterConditions.single_dual_weighted_moments_bounded
    {n a N m d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (ε : ℕ → (Fin a → ℕ) → ℝ) (hε : ∀ᶠ w in atTop, ∀ x, |ε w x| ≤ 1)
    (g : ℕ → (Fin a → ℕ) → CubeVertex d → ℤ → ℝ)
    (hg : ∀ᶠ w in atTop, ∀ x S y, |g w x S y| ≤ 1 + masterPredictionBlockMask F C label w y)
    : WeightedMomentBounded
      (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
      (fun w y => 1 + masterPredictionBlockMask F C label w y)
      (masterSingleGoodDualTest F d gap J choice tests den ε g) := by
  intro p
  have hA : 0 ≤ predictionDualThreshold d := (zero_le_one.trans (predictionDualThreshold_ge_one d))
  refine ⟨2 * predictionDualThreshold d ^ p + 1, by positivity, ?_⟩
  exact hF.normalized_single_dual_moment_eventually_le (b := p) hD C hN label tail htail
    root gap htailroot htailgap J hJ choice tests den hden masterSlot hmasterSlot hinclude
    ε hε g hg 1 (by norm_num)

end Hindman168
