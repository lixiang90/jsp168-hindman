import Hindman168.UnitriangularRationalLieLatticeSpan
import Hindman168.FiniteIntegerPeriodicCompactRange

/-! The rational subgroup lattice theorem in the abelian strict-matrix case.
Here additive closure of the actual lattice logarithms is proved from the
vanishing actual Lie bracket. Their finite spanning supplies integer
periods, and a proved periodic exponential map gives the compact
original nonnormal group quotient. No compactness premise is supplied. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set Topology

variable {n : ℕ}
local instance abelianLieLatticeMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 def unitriangularAbelianLogLattice
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0) :
    Submodule ℤ (unitriangularSubalgebraDomain V) :=
  ({
    carrier := {X | unitriangularExponential X.val ∈ integerUnitriangularLattice n}
    zero_mem' := by
      have hE : unitriangularExponential (0 : StrictUpperTriangular n ℝ) = 1 := by
        apply unitriangular_val_injective
        exact matrixFiniteExp_zero
      change unitriangularExponential (0 : StrictUpperTriangular n ℝ) ∈ integerUnitriangularLattice n
      rw [hE]
      exact (integerUnitriangularLattice n).one_mem
    add_mem' {X Y} hX hY := by
      have hc : Commute X.val.val Y.val.val := sub_eq_zero.mp
        (habel X.val.val X.property Y.val.val Y.property)
      change unitriangularExponential (X.val + Y.val) ∈ integerUnitriangularLattice n
      rw [unitriangularExponential_add_of_commute X.val Y.val hc]
      exact (integerUnitriangularLattice n).mul_mem hX hY
    neg_mem' {X} hX := by
      change unitriangularExponential (-X.val) ∈ integerUnitriangularLattice n
      rw [unitriangularExponential_neg]
      exact (integerUnitriangularLattice n).inv_mem hX
  } : AddSubgroup (unitriangularSubalgebraDomain V)).toIntSubmodule

 theorem unitriangularAbelianLogLattice_mem_iff
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0) (X : unitriangularSubalgebraDomain V) :
    X ∈ unitriangularAbelianLogLattice V habel ↔
      unitriangularExponential X.val ∈ integerUnitriangularLattice n := Iff.rfl

 theorem unitriangularAbelianLogLattice_discrete
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0) :
    DiscreteTopology (unitriangularAbelianLogLattice V habel) := by
  letI := integerUnitriangularLattice_discrete (n := n)
  let f : unitriangularAbelianLogLattice V habel → integerUnitriangularLattice n :=
    fun X => ⟨unitriangularExponential X.val.val, X.property⟩
  have hL : IsEmbedding ((↑) : unitriangularAbelianLogLattice V habel →
      unitriangularSubalgebraDomain V) := IsEmbedding.subtypeVal
  have hV : IsEmbedding ((↑) : unitriangularSubalgebraDomain V →
      StrictUpperTriangular n ℝ) := IsEmbedding.subtypeVal
  have hΓ : IsEmbedding ((↑) : integerUnitriangularLattice n → Unitriangular n ℝ) :=
    IsEmbedding.subtypeVal
  have he := (unitriangularExponentialHomeomorph (n := n) (R := ℝ)).isEmbedding.comp
    (hV.comp hL)
  have hf : IsEmbedding f := hΓ.of_comp_iff.mp he
  exact hf.discreteTopology

 theorem rationalUnitriangularAbelianLogLattice_span_top
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    span ℝ (unitriangularAbelianLogLattice V habel : Set (unitriangularSubalgebraDomain V)) = ⊤ := by
  let f : unitriangularSubalgebraDomain V →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (StrictUpperTriangular n ℝ).subtype.comp (unitriangularSubalgebraDomain V).subtype
  have heq : f '' (unitriangularAbelianLogLattice V habel : Set (unitriangularSubalgebraDomain V)) =
      unitriangularLieLatticeLogSet V hV := by
    ext X
    constructor
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨unitriangularExponential Y.val, ⟨?_, hY⟩, ?_⟩
      · change (unitriangularLogarithm (unitriangularExponential Y.val)).val ∈ V
        rw [unitriangularLogarithm_exponential]
        exact Y.property
      · change (unitriangularLogarithm (unitriangularExponential Y.val)).val = Y.val.val
        rw [unitriangularLogarithm_exponential]
    · rintro ⟨g, hg, rfl⟩
      let Y : unitriangularSubalgebraDomain V := ⟨unitriangularLogarithm g, hg.1⟩
      refine ⟨Y, ?_, rfl⟩
      change unitriangularExponential (unitriangularLogarithm g) ∈ integerUnitriangularLattice n
      rw [unitriangularExponential_logarithm]
      exact hg.2
  apply eq_top_iff.mpr
  intro X _
  have hx : f X ∈ span ℝ (f '' (unitriangularAbelianLogLattice V habel :
      Set (unitriangularSubalgebraDomain V))) := by
    rw [heq, rationalUnitriangularLieSubalgebra_lattice_log_span V hV hRat]
    exact X.property
  rw [← Submodule.map_span] at hx
  obtain ⟨Y, hY, hYX⟩ := hx
  have hEq : Y = X := Subtype.ext (Subtype.ext hYX)
  exact hEq ▸ hY

 theorem rationalUnitriangularAbelianLieLattice_quotient_compact
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    CompactSpace (unitriangularLieSubgroup V hV ⧸ integerUnitriangularLieLattice V hV) := by
  let E : unitriangularSubalgebraDomain V ≃ₜ unitriangularLieSubgroup V hV :=
    unitriangularSubalgebraExponentialHomeomorph V
  let f : unitriangularSubalgebraDomain V →
      unitriangularLieSubgroup V hV ⧸ integerUnitriangularLieLattice V hV :=
    fun X => (E X : unitriangularLieSubgroup V hV ⧸ integerUnitriangularLieLattice V hV)
  have hc := spanning_integer_periods_compact_range
    (unitriangularAbelianLogLattice V habel)
    (rationalUnitriangularAbelianLogLattice_span_top V hV habel hRat) f
    (QuotientGroup.continuous_mk.comp E.continuous) (by
      intro Z W hW
      symm
      apply QuotientGroup.eq.mpr
      change (unitriangularExponential Z.val)⁻¹ *
        unitriangularExponential (Z.val + W.val) ∈ integerUnitriangularLattice n
      have hcomm : Commute Z.val.val W.val.val := sub_eq_zero.mp
        (habel Z.val.val Z.property W.val.val W.property)
      rw [unitriangularExponential_add_of_commute Z.val W.val hcomm, inv_mul_cancel_left]
      exact hW)
  have hsurj : Function.Surjective f := QuotientGroup.mk_surjective.comp E.surjective
  rw [Set.range_eq_univ.mpr hsurj] at hc
  exact isCompact_univ_iff.mp hc

 theorem rationalUnitriangularAbelianLieLattice_quotient_closedEmbedding
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    IsClosedEmbedding (subgroupLatticeQuotientInclusion (integerUnitriangularLattice n)
      (unitriangularLieSubgroup V hV)) := by
  letI := integerUnitriangularLattice_isClosed (n := n)
  letI : CompactSpace (unitriangularLieSubgroup V hV ⧸
      (integerUnitriangularLattice n).comap (unitriangularLieSubgroup V hV).subtype) :=
    rationalUnitriangularAbelianLieLattice_quotient_compact V hV habel hRat
  exact subgroupLatticeQuotientInclusion_closedEmbedding _ _

 theorem rationalUnitriangularAbelianLieLattice_orbit_isCompact
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (habel : ∀ X ∈ V, ∀ Y ∈ V, ⁅X, Y⁆ = 0)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    IsCompact (((↑) : Unitriangular n ℝ → Unitriangular n ℝ ⧸ integerUnitriangularLattice n) ''
      (unitriangularLieSubgroup V hV : Set (Unitriangular n ℝ))) := by
  letI : CompactSpace (unitriangularLieSubgroup V hV ⧸
      (integerUnitriangularLattice n).comap (unitriangularLieSubgroup V hV).subtype) :=
    rationalUnitriangularAbelianLieLattice_quotient_compact V hV habel hRat
  exact subgroupLatticeOrbit_isCompact _ _

end Hindman168
