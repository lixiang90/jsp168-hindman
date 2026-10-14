import Hindman168.RoughTriangularBinomial
import Hindman168.RoughInterpolationPaperGrowth

namespace Hindman168
open Polynomial Filter
open scoped Topology BigOperators

theorem rough_spatial_coefficient_models
    {α κ : Type*} [Fintype κ] {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hg : PowerDominates l Z S)
    (hS : ∀ᶠ w in l, 1 ≤ S w) (hZ : ∀ᶠ w in l, 0 < Z w)
    (s : Finset (κ → ℕ)) (q H : ℕ) (hH : 2 * q + 2 ≤ H)
    (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)
    (A0 : ℝ) (hA : 0 < A0) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : (κ → ℕ) → ℝ[X])
      (p : (κ → ℕ) → ℕ → ℕ) (b : (κ → ℕ) → ℕ → κ → ℕ), 0 < m →
      (∀ r, r.Prime → r ∣ m → r ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t + m * z)) →
      (∀ I ∈ s, ((C (t : ℝ) + C (m : ℝ) * X) ^ (∑ j, I j) * theta I).natDegree ≤ q) →
      (∀ I ∈ s, ∀ z, z < H → p I z = 1 ∨ p I z = t + m * z) →
      (∀ I ∈ s, ∀ z, z < H → ∀ j, b I z j ≤ p I z) →
      (∀ I ∈ s, ∀ z, z < H →
        ‖(((p I z : ℝ) ^ (∑ j, I j) *
          (∑ J ∈ s, (roughBinomialWeight I J (b I z) : ℝ) * (theta J).eval (z : ℝ)) : ℝ) : UnitAddCircle)‖ ≤
          A0 * ((p I z : ℝ) / Z w) ^ (∑ j, I j)) →
      ∃ M : (κ → ℕ) → ℚ[X], ∀ I ∈ s,
        RoughCoefficientModel (W w) H q (∑ j, I j) (Z w)
          (roughDescentConstant q s.card A0 (2 ^ q) q) (theta I) (M I) := by
  have hh := rough_simultaneous_descent hW hg hS hZ s (fun I => ∑ j, I j)
    q H hH he A0 (2 ^ q) hA (by positivity)
  filter_upwards [hh] with w hw
  intro t m theta p b hm hmsmooth hprog hrough hdeg hp hb hobs
  apply hw t m theta p (fun I z J => roughBinomialWeight I J (b I z))
  refine ⟨hm, hmsmooth, hprog, hrough, ?_⟩
  intro I hI
  refine ⟨hdeg I hI, hp I hI, ?_, ?_⟩
  · intro z hz J hJ
    exact roughBinomialWeight_bound I J (b I z) q (p I z)
      (he J (Finset.mem_filter.mp hJ).1).2 (hb I hI z hz)
  · intro z hz
    simpa only [rough_binomial_sum_triangular s I (b I z) hI (fun J => (theta J).eval (z : ℝ))]
      using hobs I hI z hz

theorem rough_spatial_coefficient_models_paper
    {α κ : Type*} [Fintype κ] {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hS : Tendsto S l atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w / (S w) ^ a) l atTop)
    (s : Finset (κ → ℕ)) (q H : ℕ) (hH : 2 * q + 2 ≤ H)
    (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)
    (A0 : ℝ) (hA : 0 < A0) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : (κ → ℕ) → ℝ[X])
      (p : (κ → ℕ) → ℕ → ℕ) (b : (κ → ℕ) → ℕ → κ → ℕ), 0 < m →
      (∀ r, r.Prime → r ∣ m → r ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t + m * z)) →
      (∀ I ∈ s, ((C (t : ℝ) + C (m : ℝ) * X) ^ (∑ j, I j) * theta I).natDegree ≤ q) →
      (∀ I ∈ s, ∀ z, z < H → p I z = 1 ∨ p I z = t + m * z) →
      (∀ I ∈ s, ∀ z, z < H → ∀ j, b I z j ≤ p I z) →
      (∀ I ∈ s, ∀ z, z < H →
        ‖(((p I z : ℝ) ^ (∑ j, I j) *
          (∑ J ∈ s, (roughBinomialWeight I J (b I z) : ℝ) * (theta J).eval (z : ℝ)) : ℝ) : UnitAddCircle)‖ ≤
          A0 * ((p I z : ℝ) / Z w) ^ (∑ j, I j)) →
      ∃ M : (κ → ℕ) → ℚ[X], ∀ I ∈ s,
        RoughCoefficientModel (W w) H q (∑ j, I j) (Z w)
          (roughDescentConstant q s.card A0 (2 ^ q) q) (theta I) (M I) := by
  have hn : ∀ n : ℕ, 0 < n → Tendsto (fun w => Z w / S w ^ n) l atTop := by
    intro n hn
    simpa only [Real.rpow_natCast] using hr (n : ℝ) (by exact_mod_cast hn)
  obtain ⟨hg, hSone, hZ⟩ := rough_interpolation_growth_from_ratios hS hn
  exact rough_spatial_coefficient_models hW hg hSone hZ s q H hH he A0 hA

end Hindman168
