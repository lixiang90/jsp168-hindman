import Hindman168.MasterFiniteClippedTemplateLimit
import Hindman168.UniformAdmissibleInputLimit

/-!
# Uniform clipped mixed products over all admissible original dual inputs

Arbitrary admissible sequences of prime-only factors and vertex tests have
the proved actual limit. A stage-wise selection argument derives uniform
vanishing over every input and every finite profile; no rate is presumed.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

structure OriginalDualInputFamily {P b : ℕ} (dim arity : Fin P → Fin b → ℕ) where
  epsilon : ∀ p q, (Fin (arity p q) → ℕ) → ℝ
  vertexTest : ∀ p q, (Fin (arity p q) → ℕ) → CubeVertex (dim p q) → ℤ → ℝ

def OriginalDualInputFamily.Admissible {P b m : ℕ} {dim arity : Fin P → Fin b → ℕ}
    (u : OriginalDualInputFamily dim arity) (F : MasterParameterFamily)
    (C : ℕ → Chain m) (label : ℕ → Fin m) (w : ℕ) : Prop :=
  (∀ p q x, |u.epsilon p q x| ≤ 1) ∧
    (∀ p q x S y, |u.vertexTest p q x S y| ≤ 1 + masterPredictionBlockMask F C label w y)

theorem MasterParameterConditions.uniform_clipped_dual_products {n N m b d K P : ℕ}
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
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ p : Fin P, ∀ u : OriginalDualInputFamily dim arity,
      u.Admissible F C label w →
      |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
          predictionClip cut (masterReplicaGoodDualTest F (dim p) (arity p) (gap p)
            J (choice p) (tests p) (den p) (fun _ => u.epsilon p)
            (fun _ => u.vertexTest p) w q y))| < η := by
  rcases Nat.eq_zero_or_pos P with hz | hP
  · subst P
    intro η _
    exact Eventually.of_forall (fun _ p => Fin.elim0 p)
  · let p₀ : Fin P := ⟨0, hP⟩
    let u₀ : OriginalDualInputFamily dim arity := ⟨fun _ _ _ => 0, fun _ _ _ _ _ => 0⟩
    let base (_w : ℕ) := (p₀, u₀)
    let avg (w : ℕ) (input : Fin P × OriginalDualInputFamily dim arity) :=
      expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
          predictionClip cut (masterReplicaGoodDualTest F (dim input.1) (arity input.1) (gap input.1)
            J (choice input.1) (tests input.1) (den input.1) (fun _ => input.2.epsilon input.1)
            (fun _ => input.2.vertexTest input.1) w q y))
    have hbase : ∀ᶠ w in atTop, (base w).2.Admissible F C label w := by
      filter_upwards [hF.block_mask_eventually_nonneg C hN label] with w hw
      constructor
      · intro p q x
        norm_num [base, u₀]
      · intro p q x S y
        change |(0 : ℝ)| ≤ 1 + masterPredictionBlockMask F C label w y
        rw [abs_zero]
        exact add_nonneg zero_le_one (hw y)
    have hseq (input : ℕ → Fin P × OriginalDualInputFamily dim arity)
        (hi : ∀ᶠ w in atTop, (input w).2.Admissible F C label w) :
        Tendsto (fun w => avg w (input w)) atTop (𝓝 0) := by
      have heps (p : Fin P) : ∀ᶠ w in atTop, ∀ q x, |(input w).2.epsilon p q x| ≤ 1 :=
        hi.mono (fun _ hw => hw.1 p)
      have hg (p : Fin P) : ∀ᶠ w in atTop, ∀ q x S y,
          |(input w).2.vertexTest p q x S y| ≤ 1 + masterPredictionBlockMask F C label w y :=
        hi.mono (fun _ hw => hw.2 p)
      exact hF.normalized_clipped_dual_finite_template_tendsto hD dim arity hd hpos r e C hN label
        tail htail root gap htailroot htailgap hgap J hJ choice tests den hden masterSlot
        hmasterSlot hinclude (fun p w => (input w).2.epsilon p) heps
        (fun p w => (input w).2.vertexTest p) hg cut hcut (fun w => (input w).1)
    have hu := uniform_zero_of_admissible_sequences
      (fun w (input : Fin P × OriginalDualInputFamily dim arity) => input.2.Admissible F C label w)
      avg base hbase hseq
    intro η hη
    filter_upwards [hu η hη] with w hw
    intro p u hc
    exact hw (p, u) hc

end Hindman168
