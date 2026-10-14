import Hindman168.UnitriangularRationalCompactRepresentatives
import Hindman168.CompactQuotientRepresentatives

/-! The actual original lattice intersection is cocompact in every rational
strict matrix Lie subgroup, including nonabelian ones. Compactness is derived
from the constructed finite-dimensional lattice reduction, in the natural
coset topology. The inclusion is a closed embedding and the ambient orbit is
compact. This concrete matrix result is not an arbitrary Lie-group or
arbitrary specified-lattice transfer theorem. -/

noncomputable section
namespace Hindman168
open Matrix Set Topology

variable {n : ℕ}
local instance rationalQuotientMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 theorem rationalUnitriangularLieLattice_quotient_compact
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    CompactSpace (unitriangularLieSubgroup V hV ⧸ integerUnitriangularLieLattice V hV) := by
  obtain ⟨K, hK, hsub, hrep⟩ := rationalUnitriangularLieSubalgebra_compact_representatives V hV hRat
  let H := unitriangularLieSubgroup V hV
  let KH : Set H := ((↑) : H → Unitriangular n ℝ) ⁻¹' K
  have hKR : K ⊆ range ((↑) : H → Unitriangular n ℝ) := by
    intro x hx
    exact ⟨⟨x, hsub hx⟩, rfl⟩
  have hKH : IsCompact KH :=
    IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKR
  apply compactSpace_of_lattice_representatives (integerUnitriangularLieLattice V hV) KH hKH
  intro g
  obtain ⟨x, hx, γ, hγ, heq⟩ := hrep g.val g.property
  have hγH : γ ∈ H := by
    have hEq : γ = x⁻¹ * g.val := by rw [heq]; simp only [inv_mul_cancel_left]
    rw [hEq]
    exact H.mul_mem (H.inv_mem (hsub hx)) g.property
  exact ⟨⟨x, hsub hx⟩, hx, ⟨γ, hγH⟩, hγ, Subtype.ext heq⟩

 theorem rationalUnitriangularLieLattice_quotient_closedEmbedding
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    IsClosedEmbedding (subgroupLatticeQuotientInclusion (integerUnitriangularLattice n)
      (unitriangularLieSubgroup V hV)) := by
  letI := integerUnitriangularLattice_isClosed (n := n)
  letI : CompactSpace (unitriangularLieSubgroup V hV ⧸
      (integerUnitriangularLattice n).comap (unitriangularLieSubgroup V hV).subtype) :=
    rationalUnitriangularLieLattice_quotient_compact V hV hRat
  exact subgroupLatticeQuotientInclusion_closedEmbedding _ _

 theorem rationalUnitriangularLieLattice_orbit_isCompact
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    IsCompact (((↑) : Unitriangular n ℝ → Unitriangular n ℝ ⧸ integerUnitriangularLattice n) ''
      (unitriangularLieSubgroup V hV : Set (Unitriangular n ℝ))) := by
  letI : CompactSpace (unitriangularLieSubgroup V hV ⧸
      (integerUnitriangularLattice n).comap (unitriangularLieSubgroup V hV).subtype) :=
    rationalUnitriangularLieLattice_quotient_compact V hV hRat
  exact subgroupLatticeOrbit_isCompact _ _

 theorem rationalUnitriangularLieLattice_quotient_metrizable
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    TopologicalSpace.MetrizableSpace
      (unitriangularLieSubgroup V hV ⧸ integerUnitriangularLieLattice V hV) := by
  letI := unitriangular_secondCountable (n := n)
  letI : SecondCountableTopology (unitriangularLieSubgroup V hV) :=
    (show IsEmbedding ((↑) : unitriangularLieSubgroup V hV → Unitriangular n ℝ) from
      IsEmbedding.subtypeVal).secondCountableTopology
  letI := integerUnitriangularLieLattice_isClosed V hV
  letI := rationalUnitriangularLieLattice_quotient_compact V hV hRat
  exact compactClosedCosetQuotient_metrizable _

end Hindman168
