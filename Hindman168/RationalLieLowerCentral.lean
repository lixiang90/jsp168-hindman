import Hindman168.RationalLinearOperations
import Hindman168.RationalLinearQuotient
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative

/-! Rationality of the actual Lie-algebra lower central series. The rational
structure must be closed under its actual bracket. No claim about the noncommutative group lattice, its exponential map,
or a topology on the group is made. -/

namespace Hindman168
open Submodule

variable {E : Type*} [LieRing E] [LieAlgebra ℝ E]
local instance realEndLieRing : LieRing (Module.End ℝ E) := LieRing.ofAssociativeRing
variable [Module ℚ E]

omit [Module ℚ E] in
/-- The actual Lie-ideal bracket agrees with the bilinear submodule image. -/
theorem lieIdeal_bracket_eq_map₂ (I : LieIdeal ℝ E) (N : LieIdeal ℝ E) :
    ((⁅I, N⁆ : LieIdeal ℝ E) : Submodule ℝ E) = map₂ (LieAlgebra.ad ℝ E).toLinearMap I N := by
  simp only [LieIdeal.toLieSubalgebra_toSubmodule]
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span', map₂_eq_span_image2]
  congr 1

/-- All actual Lie lower-central layers are rational when the specified
rational structure spans the ambient space and is closed under brackets. -/
theorem lieLowerCentral_rational (L : Submodule ℤ E)
    (hL : span ℝ (L : Set E) = ⊤)
    (hbr : ∀ x ∈ span ℚ (L : Set E), ∀ y ∈ span ℚ (L : Set E),
      ⁅x, y⁆ ∈ span ℚ (L : Set E)) (k : ℕ) :
    RationalLinearSubspace L (LieModule.lowerCentralSeries ℝ E E k : Submodule ℝ E) := by
  induction k with
  | zero =>
    rw [LieModule.lowerCentralSeries_zero]
    change RationalLinearSubspace L (⊤ : Submodule ℝ E)
    exact rationalLinearSubspace_top L hL
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ, lieIdeal_bracket_eq_map₂]
    exact rationalLinearSubspace_map₂ L (LieAlgebra.ad ℝ E).toLinearMap hbr
      ⊤ _ (rationalLinearSubspace_top L hL) ih

/-- The original integer intersection spans every actual lower-central
Lie-algebra layer. -/
theorem lieLowerCentral_integer_span (L : Submodule ℤ E)
    (hL : span ℝ (L : Set E) = ⊤)
    (hbr : ∀ x ∈ span ℚ (L : Set E), ∀ y ∈ span ℚ (L : Set E),
      ⁅x, y⁆ ∈ span ℚ (L : Set E)) (k : ℕ) :
    span ℝ ((LieModule.lowerCentralSeries ℝ E E k : Set E) ∩ (L : Set E)) =
      (LieModule.lowerCentralSeries ℝ E E k : Submodule ℝ E) :=
  rationalLinearSubspace_integer_span L _ (lieLowerCentral_rational L hL hbr k)

/-- A genuine linear coordinate realization of a lower-central Lie layer
has compact additive quotient by the realized integer intersection. The
coordinate lattice is explicitly required discrete. This is not a claim
that logarithms of an arbitrary group lattice form an additive lattice. -/
theorem lieLowerCentral_coordinate_quotient_compact {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Module ℚ X] [FiniteDimensional ℝ X]
    (f : E ≃ₗ[ℝ] X) (L : Submodule ℤ E)
    [DiscreteTopology (L.map (f.restrictScalars ℤ).toLinearMap)]
    (hL : span ℝ (L : Set E) = ⊤)
    (hbr : ∀ x ∈ span ℚ (L : Set E), ∀ y ∈ span ℚ (L : Set E),
      ⁅x, y⁆ ∈ span ℚ (L : Set E)) (k : ℕ) :
    CompactSpace (((LieModule.lowerCentralSeries ℝ E E k : Submodule ℝ E).map f.toLinearMap) ⧸
      linearLayerLattice (L.map (f.restrictScalars ℤ).toLinearMap)
        ((LieModule.lowerCentralSeries ℝ E E k : Submodule ℝ E).map f.toLinearMap)) := by
  have hr := rationalLinearSubspace_map L _ (lieLowerCentral_rational L hL hbr k) f.toLinearMap
  exact rationalLinearSubspace_quotient_compact _ _ hr

/-- The actual additive coordinate-layer orbit is embedded and compact via
the natural quotient maps. No group exponential comparison is used. -/
theorem lieLowerCentral_coordinate_orbit_closedEmbedding {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Module ℚ X] [FiniteDimensional ℝ X]
    (f : E ≃ₗ[ℝ] X) (L : Submodule ℤ E)
    [DiscreteTopology (L.map (f.restrictScalars ℤ).toLinearMap)]
    (hL : span ℝ (L : Set E) = ⊤)
    (hbr : ∀ x ∈ span ℚ (L : Set E), ∀ y ∈ span ℚ (L : Set E),
      ⁅x, y⁆ ∈ span ℚ (L : Set E)) (k : ℕ) :
    Topology.IsClosedEmbedding (linearLayerQuotientInclusion
      (L.map (f.restrictScalars ℤ).toLinearMap)
      ((LieModule.lowerCentralSeries ℝ E E k : Submodule ℝ E).map f.toLinearMap)) := by
  have hr := rationalLinearSubspace_map L _ (lieLowerCentral_rational L hL hbr k) f.toLinearMap
  exact rationalLinearSubspace_quotient_closedEmbedding _ _ hr

end Hindman168
