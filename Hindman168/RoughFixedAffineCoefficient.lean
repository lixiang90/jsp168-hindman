import Hindman168.RoughAffineBinomialCoefficient
import Hindman168.RoughFiniteCoefficientAssembly

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_fixed_affine_coefficient {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (theta : (κ → ℕ) → ℝ) (c : ℝ)
    (b : κ → ℕ) (p : ℕ) (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => (p : ℝ))
        (roughSpatialFixedPolynomial (roughFiniteMultiindices s) c (fun J => theta J))) =
      (p : ℝ)^(∑ j, I j)*∑ J ∈ s, (roughBinomialWeight I J b : ℝ)*theta J := by
  rw [roughSpatialFixedPolynomial, roughFiniteMultiindices, Finset.sum_map]
  exact rough_affine_positive_binomial_coefficient s theta c b p I hI

end Hindman168
