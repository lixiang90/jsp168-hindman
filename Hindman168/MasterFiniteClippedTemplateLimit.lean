import Hindman168.MasterClippedDualProductLimit

/-!
# One common clipping bound across finite original dual template profiles

The common dimension bound supplies a fixed clipping threshold. Arbitrary
stage-wise choice among finitely many profiles preserves the actual clipped
root-centered product limit under the same master family.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem predictionDualThreshold_mono {a d : ℕ} (had : a ≤ d) :
    predictionDualThreshold a ≤ predictionDualThreshold d := by
  unfold predictionDualThreshold
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) had) 1)

theorem MasterParameterConditions.normalized_clipped_dual_finite_template_tendsto {n N m b d K P : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (dim arity : Fin P → Fin b → ℕ) (hd : ∀ p q, dim p q ≤ d) (hpos : ∀ p q, 0 < dim p q)
    (r : Fin P → ℕ) (e : ∀ p, (Σ q, Fin (arity p q)) ≃ Fin (r p))
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (gap : Fin P → ℕ → Fin b → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ p, ∀ᶠ w in atTop, ∀ q, tail w ⊆ Finset.range (gap p w q).val)
    (hgap : ∀ p, ∀ᶠ w in atTop, ∀ q, (gap p w q).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ a, 1 ≤ J a) (choice : Fin P → ℕ → Fin b → Fin K)
    (tests : ∀ p q, Finset (MvPolynomial (Fin (arity p q)) ℤ))
    (den : ∀ p q, MvPolynomial (Fin (arity p q)) ℤ) (hden : ∀ p q, den p q ∈ tests p q)
    (masterSlot : ∀ p q, Fin (arity p q) → Fin n)
    (hmasterSlot : ∀ p q, Function.Injective (masterSlot p q))
    (hinclude : ∀ p q f, f ∈ tests p q → MvPolynomial.rename (masterSlot p q) f ∈ D)
    (ε : ∀ p, ℕ → ∀ q, (Fin (arity p q) → ℕ) → ℝ)
    (hε : ∀ p, ∀ᶠ w in atTop, ∀ q x, |ε p w q x| ≤ 1)
    (g : ∀ p, ℕ → ∀ q, (Fin (arity p q) → ℕ) → CubeVertex (dim p q) → ℤ → ℝ)
    (hg : ∀ p, ∀ᶠ w in atTop, ∀ q x S y,
      |g p w q x S y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut)
    (profile : ℕ → Fin P) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
        predictionClip cut (masterReplicaGoodDualTest F (dim (profile w)) (arity (profile w)) (gap (profile w))
          J (choice (profile w)) (tests (profile w)) (den (profile w)) (ε (profile w)) (g (profile w)) w q y)))
      atTop (𝓝 0) := by
  let avg p w := expectation (integerMass (F.cutoff w (root w).val) (primorial w))
    (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
      predictionClip cut (masterReplicaGoodDualTest F (dim p) (arity p) (gap p) J (choice p) (tests p) (den p) (ε p) (g p) w q y))
  have hall (p : Fin P) : Tendsto (avg p) atTop (𝓝 0) :=
    hF.normalized_clipped_dual_product_tendsto hD (dim p) (arity p) (hd p) (hpos p) (e p)
      C hN label tail htail root (gap p) htailroot (htailgap p) (hgap p) J hJ (choice p)
      (tests p) (den p) (hden p) (masterSlot p) (hmasterSlot p) (hinclude p) (ε p) (hε p) (g p) (hg p)
      (fun _ => cut) (fun q => (predictionDualThreshold_mono (hd p q)).trans_lt hcut)
  exact finite_dual_real_choice_tendsto avg hall profile

end Hindman168
