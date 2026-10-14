import Hindman168.MasterEmptyDualProductLimit

/-!
# All fixed replica counts and finite varying dual template choices

The empty product uses actual mask mean one. Positive products use the
normalized cube theorem. Finite template selection retains one and the
same master family: its fixed local polynomial list and arity do not grow
with the number of independent replicas or the stage-wise template choice.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem finite_dual_real_choice_tendsto {ι : Type*} [Finite ι]
    (f : ι → ℕ → ℝ) (h : ∀ i, Tendsto (f i) atTop (𝓝 0)) (choice : ℕ → ι) :
    Tendsto (fun w => f (choice w) w) atTop (𝓝 0) := by
  apply tendsto_def.mpr
  intro S hS
  have hall := eventually_all.mpr (fun i => (h i).eventually hS)
  filter_upwards [hall] with w hw
  exact hw (choice w)

theorem MasterParameterConditions.normalized_dual_product_all_b_tendsto {n r N m b d K : ℕ}
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
    (hg : ∀ᶠ w in atTop, ∀ q x S y, |g w q x S y| ≤ 1 + masterPredictionBlockMask F C label w y) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (masterPredictionBlockMask F C label w y - 1) *
        ∏ q, masterReplicaGoodDualTest F dim arity gap J choice tests den ε g w q y))
      atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos b with hz | hb
  · subst b
    simpa using hF.empty_dual_product_tendsto C hN label tail htail root htailroot
  · exact hF.normalized_dual_product_tendsto hD hb dim arity hd hpos e C hN label tail htail
      root gap htailroot htailgap hgap J hJ choice tests den hden masterSlot hmasterSlot hinclude ε hε g hg

theorem MasterParameterConditions.normalized_dual_finite_template_tendsto {n N m b d K P : ℕ}
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
    (profile : ℕ → Fin P) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
        masterReplicaGoodDualTest F (dim (profile w)) (arity (profile w)) (gap (profile w))
          J (choice (profile w)) (tests (profile w)) (den (profile w)) (ε (profile w)) (g (profile w)) w q y))
      atTop (𝓝 0) := by
  let avg p w := expectation (integerMass (F.cutoff w (root w).val) (primorial w))
    (fun y => (masterPredictionBlockMask F C label w y - 1) * ∏ q,
      masterReplicaGoodDualTest F (dim p) (arity p) (gap p) J (choice p) (tests p) (den p) (ε p) (g p) w q y)
  have hall (p : Fin P) : Tendsto (avg p) atTop (𝓝 0) :=
    hF.normalized_dual_product_all_b_tendsto hD (dim p) (arity p) (hd p) (hpos p) (e p)
      C hN label tail htail root (gap p) htailroot (htailgap p) (hgap p) J hJ (choice p)
      (tests p) (den p) (hden p) (masterSlot p) (hmasterSlot p) (hinclude p) (ε p) (hε p) (g p) (hg p)
  exact finite_dual_real_choice_tendsto avg hall profile

end Hindman168
