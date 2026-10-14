import Hindman168.RoughFixedAffineCoefficient
import Hindman168.RoughSpatialCoefficientModels

namespace Hindman168
open Polynomial Filter
open scoped Topology BigOperators

theorem rough_actual_affine_obstruction_models
    {α κ : Type*} [Fintype κ] {l : Filter α} {W : α → ℕ} (hW : Tendsto W l atTop)
    {S Z : α → ℝ} (hS : Tendsto S l atTop)
    (hr : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(S w)^a) l atTop)
    (s : Finset (κ → ℕ)) (q H : ℕ) (hH : 2*q+2 ≤ H)
    (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)
    (A0 : ℝ) (hA : 0 < A0) :
    ∀ᶠ w in l, ∀ (t m : ℕ) (theta : (κ → ℕ) → ℝ[X]) (P0 : ℝ[X])
      (p : (κ → ℕ) → ℕ → ℕ) (b : (κ → ℕ) → ℕ → κ → ℕ), 0 < m →
      (∀ r, r.Prime → r ∣ m → r ≤ W w) →
      (∀ z : ℕ, z < H → S w ≤ (t+m*z : ℕ) ∧ (t+m*z : ℕ) < 2*S w) →
      (∀ z : ℕ, z < H → (primorial (W w)).Coprime (t+m*z)) →
      (∀ I ∈ s, ((C (t : ℝ)+C (m : ℝ)*X)^(∑ j, I j)*theta I).natDegree ≤ q) →
      (∀ I ∈ s, ∀ z, z < H → p I z = 1 ∨ p I z = t+m*z) →
      (∀ I ∈ s, ∀ z, z < H → ∀ j, b I z j ≤ p I z) →
      (∀ I ∈ s, ∀ z, z < H →
        ‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm I)
          (roughMvAffineSubstitution (fun j => (b I z j : ℝ)) (fun _ => (p I z : ℝ))
            (roughSpatialFixedPolynomial (roughFiniteMultiindices s) (P0.eval (z : ℝ))
              (fun J => (theta J).eval (z : ℝ)))) : ℝ) : UnitAddCircle)‖ ≤
          A0*((p I z : ℝ)/Z w)^(∑ j, I j)) →
      ∃ M : (κ → ℕ) → ℚ[X], ∀ I ∈ s,
        RoughCoefficientModel (W w) H q (∑ j, I j) (Z w)
          (roughDescentConstant q s.card A0 (2^q) q) (theta I) (M I) := by
  filter_upwards [rough_spatial_coefficient_models_paper hW hS hr s q H hH he A0 hA] with w hw
  intro t m theta P0 p b hm hsmooth hprog hrough hdeg hp hb hobs
  apply hw t m theta p b hm hsmooth hprog hrough hdeg hp hb
  intro I hI z hz
  rw [← rough_fixed_affine_coefficient s (fun J => (theta J).eval (z : ℝ))
    (P0.eval (z : ℝ)) (b I z) (p I z) I (he I hI).1]
  exact hobs I hI z hz

end Hindman168
