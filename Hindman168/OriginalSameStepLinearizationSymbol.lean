import Hindman168.OriginalSameStepLinearizationCalculus
import OAI.Combinatorics.Progressions.Estimates.AdaptedTranslation
/-!
# The first shifted polynomial symbol

Derived from OpenAI math, fixed commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0.
Source: lean/OAI/Combinatorics/Progressions/Polynomial/ShiftedPolynomialBasis.lean,
154–186, 209–218.
Modified by moving these complete proofs to an independent namespace and
making their field notation explicit. All original filtration, polynomial
and ideal types are reused; no assumption or conclusion is changed.
-/
namespace Hindman168.OriginalSameStepLinearization.Symbols
open OAI.Erdos3 OAI.Erdos3.VectorPolynomial
variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)
abbrev PolynomialSymbol (w : σ → ℕ) :=
  F.adaptedLieSubalgebra w ⧸ F.shiftedAdaptedIdeal w

noncomputable def polynomialSymbolMap (w : σ → ℕ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ PolynomialSymbol F w :=
  lieQuotientMap (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_surjective (w : σ → ℕ) :
    Function.Surjective (polynomialSymbolMap F w) :=
  lieQuotientMap_surjective (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_eq_zero_iff (w : σ → ℕ) (p : F.adaptedLieSubalgebra w) :
    polynomialSymbolMap F w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 1) :=
  lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) p

theorem polynomialSymbolMap_eq_iff (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    polynomialSymbolMap F w p = polynomialSymbolMap F w q ↔
      ∀ α, coefficients ((p : VectorPolynomial σ ℚ L) - (q : VectorPolynomial σ ℚ L)) α ∈
        F.layer (Finsupp.weight w α + 1) := by
  rw [← sub_eq_zero, ← map_sub, polynomialSymbolMap_eq_zero_iff F]
  rfl

theorem polynomialSymbolMap_lieBCH (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    polynomialSymbolMap F w (lieBCH s p q) =
      lieBCH s (polynomialSymbolMap F w p) (polynomialSymbolMap F w q) :=
  map_lieBCH (polynomialSymbolMap F w) s p q

theorem polynomialSymbol_lowerCentralSeries_eq_bot (w : σ → ℕ) :
    LieModule.lowerCentralSeries ℚ (PolynomialSymbol F w) (PolynomialSymbol F w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (p : F.adaptedLieSubalgebra w) :
    polynomialSymbolMap F w
      ⟨translate h (p : VectorPolynomial σ ℚ L),
        (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h
          ((F.mem_adaptedSubmodule w _).mp p.property))⟩ =
      polynomialSymbolMap F w p := by
  apply (polynomialSymbolMap_eq_iff F w _ p).mpr
  exact F.translate_sub_coefficient_mem w hw h ((F.mem_adaptedSubmodule w _).mp p.property)

end Hindman168.OriginalSameStepLinearization.Symbols
