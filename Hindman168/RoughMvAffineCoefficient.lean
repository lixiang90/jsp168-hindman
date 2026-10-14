import Hindman168.RoughMvAffineMonomialCoefficient

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_mv_affine_monomial_coefficient {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b k : κ → R) (I : κ → ℕ) (J : κ →₀ ℕ) (a : R) :
    coeff (Finsupp.equivFunOnFinite.symm I) (roughMvAffineSubstitution b k (monomial J a)) =
      a*roughAffinePowerCoefficient b k I J := by
  rw [roughMvAffineSubstitution, eval₂Hom_monomial, coeff_C_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [rough_affine_monomial_coefficient]

theorem rough_mv_affine_coefficient {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b k : κ → R) (I : κ → ℕ) (p : MvPolynomial κ R) :
    coeff (Finsupp.equivFunOnFinite.symm I) (roughMvAffineSubstitution b k p) =
      ∑ J ∈ p.support, coeff J p*roughAffinePowerCoefficient b k I J := by
  calc
    _ = coeff (Finsupp.equivFunOnFinite.symm I)
        (roughMvAffineSubstitution b k (∑ J ∈ p.support, monomial J (coeff J p))) :=
      congrArg (fun f => coeff (Finsupp.equivFunOnFinite.symm I) (roughMvAffineSubstitution b k f)) p.as_sum
    _ = _ := by
      rw [map_sum, coeff_sum]
      simp_rw [rough_mv_affine_monomial_coefficient]

end Hindman168
