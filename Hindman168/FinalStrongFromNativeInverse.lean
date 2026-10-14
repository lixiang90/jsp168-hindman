import Hindman168.FinalUniformAlignment
import Hindman168.FinalStrongFromPrinciples

/-! The original StrongConjecture now has only the genuine higher-order
native interval inverse family as an analytic input. Uniform Alignment,
including its pre-model quantifier order, has been proved. -/
namespace Hindman168
universe u

theorem finiteConjecture_of_native_inverse
    (hinverse : ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t-1) t) :
    FiniteConjecture :=
  finiteConjecture_of_native_inverse_and_alignment hinverse hasUniformSelectedPrincipalAlignment

theorem strongConjecture_of_native_inverse
    (hinverse : ∀ t : ℕ, 2 ≤ t → HasNativePeriodicIntervalInverse.{u} (t-1) t) :
    StrongConjecture :=
  strongConjecture_of_native_inverse_and_alignment hinverse hasUniformSelectedPrincipalAlignment

end Hindman168
