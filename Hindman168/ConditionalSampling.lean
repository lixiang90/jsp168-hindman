import Hindman168.UniformIntervalTranslation

/-!
# Conditional sampling with arbitrary finite outside variables

The bounds are averaged against the outside probability law. In
particular, bounds uniform in the outside variables survive conditioning
and unconditioning with the same constant. Actual PMF bind coefficients
are proved equal to the finite mixture coefficients.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators

theorem mixture_constant {α ι : Type*} (S : Finset ι) (p : ι → ℝ) (ν : Mass α) :
    mixture S p (fun _ => ν) = (∑ i ∈ S, p i) • ν := by
  ext x
  rw [mixture_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_mul]

theorem mixture_probability_total {α ι : Type*} (ρ : Mass ι)
    (htρ : total ρ = 1) (μ : ι → Mass α) (htμ : ∀ i, total (μ i) = 1) :
    total (mixture ρ.support (fun i => ρ i) μ) = 1 := by
  rw [mixture_total]
  simp only [htμ, mul_one]
  exact htρ

theorem toPMF_bind {α ι : Type*} (ρ : Mass ι) (hρ : ∀ i, 0 ≤ ρ i)
    (htρ : total ρ = 1) (μ : ι → Mass α) (hμ : ∀ i a, 0 ≤ μ i a)
    (htμ : ∀ i, total (μ i) = 1) :
    (toPMF ρ hρ htρ).bind (fun i => toPMF (μ i) (hμ i) (htμ i)) =
      toPMF (mixture ρ.support (fun i => ρ i) μ)
        (mixture_nonneg (fun i _ => hρ i) (fun i _ a => hμ i a))
        (mixture_probability_total ρ htρ μ htμ) := by
  ext a
  rw [toPMF_bind_apply, toPMF_apply]

theorem conditional_distance_uniform {α ι : Type*} (ρ : Mass ι)
    (hρ : ∀ i, 0 ≤ ρ i) (htρ : total ρ = 1) (μ ν : ι → Mass α)
    {E : ℝ} (he : ∀ i ∈ ρ.support, distance (μ i) (ν i) ≤ E) :
    distance (mixture ρ.support (fun i => ρ i) μ)
      (mixture ρ.support (fun i => ρ i) ν) ≤ E :=
  mixture_distance_uniform μ ν (fun i _ => hρ i) htρ he

theorem conditional_distance_fixed {α ι : Type*} (ρ : Mass ι)
    (hρ : ∀ i, 0 ≤ ρ i) (htρ : total ρ = 1) (μ : ι → Mass α) (ν : Mass α)
    {E : ℝ} (he : ∀ i ∈ ρ.support, distance (μ i) ν ≤ E) :
    distance (mixture ρ.support (fun i => ρ i) μ) ν ≤ E := by
  have hc : mixture ρ.support (fun i => ρ i) (fun _ => ν) = ν := by
    rw [mixture_constant, show (∑ i ∈ ρ.support, ρ i) = 1 from htρ, one_smul]
  exact hc ▸ conditional_distance_uniform ρ hρ htρ μ (fun _ => ν) he

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators

theorem conditional_interval_residue_distance {ι : Type*} (ρ : FiniteMass.Mass ι)
    (hρ : ∀ i, 0 ≤ ρ i) (htρ : FiniteMass.total ρ = 1)
    (A : ι → ℤ) (T : ι → ℕ) {k : ℕ} (hk : 0 < k)
    (hT : ∀ i ∈ ρ.support, 0 < T i) {E : ℝ}
    (he : ∀ i ∈ ρ.support, (k : ℝ) / T i ≤ E) :
    FiniteMass.distance
      (FiniteMass.mixture ρ.support (fun i => ρ i) (fun i => intervalResidueMass (A i) (T i) k hk))
      (uniformResidueMass k) ≤ E := by
  apply FiniteMass.conditional_distance_fixed ρ hρ htρ
  intro i hi
  exact (uniform_interval_residue_distance (A i) (hT i hi) hk).trans (he i hi)

theorem conditional_interval_translation_distance {ι : Type*} (ρ : FiniteMass.Mass ι)
    (hρ : ∀ i, 0 ≤ ρ i) (htρ : FiniteMass.total ρ = 1)
    (A : ι → ℤ) (T : ι → ℕ) (u : ι → ℤ)
    (hT : ∀ i ∈ ρ.support, 0 < T i) {E : ℝ}
    (he : ∀ i ∈ ρ.support, 2 * |(u i : ℝ)| / T i ≤ E) :
    FiniteMass.distance
      (FiniteMass.mixture ρ.support (fun i => ρ i)
        (fun i => (uniformIntervalMass (A i) (T i)).mapDomain (fun z => z + u i)))
      (FiniteMass.mixture ρ.support (fun i => ρ i) (fun i => uniformIntervalMass (A i) (T i))) ≤ E := by
  apply FiniteMass.conditional_distance_uniform ρ hρ htρ
  intro i hi
  exact (uniform_interval_translation_linear (A i) (hT i hi) (u i)).trans (he i hi)

theorem conditional_interval_residue_PMF_apply {ι : Type*} (ρ : FiniteMass.Mass ι)
    (hρ : ∀ i, 0 ≤ ρ i) (htρ : FiniteMass.total ρ = 1)
    (A : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i)
    {k : ℕ} (hk : 0 < k) (a : Fin k) :
    ((FiniteMass.toPMF ρ hρ htρ).bind
      (fun i => (uniformIntervalPMF (A i) (T i) (hT i)).map (integerResidue k hk))) a =
      ENNReal.ofReal (FiniteMass.mixture ρ.support (fun i => ρ i)
        (fun i => intervalResidueMass (A i) (T i) k hk) a) := by
  have hm (i : ι) :
      (uniformIntervalPMF (A i) (T i) (hT i)).map (integerResidue k hk) =
        FiniteMass.toPMF (intervalResidueMass (A i) (T i) k hk)
          (FiniteMass.push_nonneg _ _ (uniformIntervalMass_nonneg (A i) (T i)))
          (by rw [intervalResidueMass, FiniteMass.total_push, uniformIntervalMass_total _ (hT i)]) :=
    FiniteMass.toPMF_map _ _ _ _
  simp only [hm]
  exact FiniteMass.toPMF_bind_apply ρ hρ htρ _ _ _ a

end Hindman168
