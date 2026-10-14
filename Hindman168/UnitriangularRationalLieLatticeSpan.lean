import Hindman168.UnitriangularRationalExponentialDenominators
import Hindman168.UnitriangularLieSubgroupBCH
import Hindman168.UnitriangularDepthLattice

/-! Rationality relative to the rational span of the actual original group
lattice logarithms. Clearing exponential denominators proves that the
logarithms of the genuine subgroup-lattice intersection span the whole Lie
subalgebra. Neither additive closure of those logarithms nor noncommutative
cocompactness is assumed or inferred from that spanning statement alone. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ}
local instance rationalLieLatticeMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 def rationalMatrixCastLinear (n : ℕ) :
    Matrix (Fin n) (Fin n) ℚ →ₗ[ℚ] Matrix (Fin n) (Fin n) ℝ where
  toFun := (algebraMap ℚ ℝ).mapMatrix
  map_add' := map_add _
  map_smul' := map_rat_smul _

 def unitriangularLatticeLogSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  (fun g : Unitriangular n ℝ => (unitriangularLogarithm g).val) ''
    (integerUnitriangularLattice n : Set (Unitriangular n ℝ))

 def unitriangularLatticeRationalStructure (n : ℕ) :
    Submodule ℚ (Matrix (Fin n) (Fin n) ℝ) :=
  span ℚ (unitriangularLatticeLogSet n)

 def RationalUnitriangularLieSubalgebra
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  span ℝ ((V : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
    (unitriangularLatticeRationalStructure n : Set (Matrix (Fin n) (Fin n) ℝ))) = V.toSubmodule

 def integerUnitriangularLieLattice
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) :
    Subgroup (unitriangularLieSubgroup V hV) :=
  (integerUnitriangularLattice n).comap (unitriangularLieSubgroup V hV).subtype

 def unitriangularLieLatticeLogSet
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  (fun g : Unitriangular n ℝ => (unitriangularLogarithm g).val) ''
    ((unitriangularLieSubgroup V hV : Set (Unitriangular n ℝ)) ∩
      (integerUnitriangularLattice n : Set (Unitriangular n ℝ)))

 theorem unitriangularLatticeRationalStructure_le_cast_range :
    unitriangularLatticeRationalStructure n ≤ (rationalMatrixCastLinear n).range := by
  apply span_le.mpr
  rintro X ⟨g, hg, rfl⟩
  obtain ⟨A, hA⟩ := integerUnitriangularLattice_log_rational g hg
  exact ⟨A.val, congrArg Subtype.val hA⟩

 theorem unitriangularLatticeRationalStructure_strict_preimage
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ unitriangularLatticeRationalStructure n) (hstrict : MatrixDepth 1 X) :
    ∃ A : StrictUpperTriangular n ℚ,
      (strictUpperTriangularMap (algebraMap ℚ ℝ) A).val = X := by
  obtain ⟨B, hB⟩ := unitriangularLatticeRationalStructure_le_cast_range hX
  have hs : MatrixDepth 1 B := by
    intro i j hij
    apply (algebraMap ℚ ℝ).injective
    change algebraMap ℚ ℝ (B i j) = algebraMap ℚ ℝ 0
    rw [map_zero]
    have hb : algebraMap ℚ ℝ (B i j) = X i j := congrFun (congrFun hB i) j
    rw [hb]
    exact hstrict i j hij
  exact ⟨⟨B, hs⟩, hB⟩

 theorem unitriangularLatticeRationalStructure_strict {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ unitriangularLatticeRationalStructure n) : MatrixDepth 1 X := by
  have hle : unitriangularLatticeRationalStructure n ≤
      (StrictUpperTriangular n ℝ).restrictScalars ℚ := by
    apply span_le.mpr
    rintro X ⟨g, _, rfl⟩
    exact (unitriangularLogarithm g).property
  exact hle hX

 theorem rationalStrictMatrix_mem_latticeRationalStructure (A : StrictUpperTriangular n ℚ) :
    (strictUpperTriangularMap (algebraMap ℚ ℝ) A).val ∈
      unitriangularLatticeRationalStructure n := by
  obtain ⟨D, hD, hp⟩ := unitriangular_rational_exponential_lattice A
  let X := strictUpperTriangularMap (algebraMap ℚ ℝ) A
  have he : unitriangularExponential ((D : ℝ) • X) ∈ integerUnitriangularLattice n := by
    simpa only [Int.cast_one, mul_one] using hp 1
  have hm : (D : ℝ) • X.val ∈ unitriangularLatticeRationalStructure n := by
    apply subset_span
    refine ⟨unitriangularExponential ((D : ℝ) • X), he, ?_⟩
    change (unitriangularLogarithm (unitriangularExponential ((D : ℝ) • X))).val = _
    rw [unitriangularLogarithm_exponential]
    rfl
  rw [Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℚ] at hm
  exact (smul_mem_iff _ (by exact_mod_cast hD.ne' : (D : ℚ) ≠ 0)).mp hm

 theorem unitriangularLatticeRationalStructure_mem_iff (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ unitriangularLatticeRationalStructure n ↔
      ∃ A : StrictUpperTriangular n ℚ,
        (strictUpperTriangularMap (algebraMap ℚ ℝ) A).val = X := by
  constructor
  · intro hx
    exact unitriangularLatticeRationalStructure_strict_preimage hx
      (unitriangularLatticeRationalStructure_strict hx)
  · rintro ⟨A, rfl⟩
    exact rationalStrictMatrix_mem_latticeRationalStructure A

 theorem integerUnitriangularLieLattice_discrete
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) :
    DiscreteTopology (integerUnitriangularLieLattice V hV) := by
  letI := integerUnitriangularLattice_discrete (n := n)
  let f : integerUnitriangularLieLattice V hV → integerUnitriangularLattice n :=
    fun g => ⟨g.val.val, g.property⟩
  have h1 : Topology.IsEmbedding ((↑) : integerUnitriangularLieLattice V hV →
      unitriangularLieSubgroup V hV) := Topology.IsEmbedding.subtypeVal
  have h2 : Topology.IsEmbedding ((↑) : unitriangularLieSubgroup V hV →
      Unitriangular n ℝ) := Topology.IsEmbedding.subtypeVal
  have h3 : Topology.IsEmbedding ((↑) : integerUnitriangularLattice n →
      Unitriangular n ℝ) := Topology.IsEmbedding.subtypeVal
  have hf : Topology.IsEmbedding f := h3.of_comp_iff.mp (h2.comp h1)
  exact hf.discreteTopology

 theorem integerUnitriangularLieLattice_isClosed
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) :
    IsClosed (integerUnitriangularLieLattice V hV : Set (unitriangularLieSubgroup V hV)) :=
  (integerUnitriangularLattice_isClosed (n := n)).preimage continuous_subtype_val

 theorem rationalUnitriangularLieSubalgebra_lattice_log_span
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    span ℝ (unitriangularLieLatticeLogSet V hV) = V.toSubmodule := by
  apply le_antisymm
  · apply span_le.mpr
    rintro X ⟨g, hg, rfl⟩
    exact hg.1
  · calc V.toSubmodule = span ℝ ((V : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
           (unitriangularLatticeRationalStructure n : Set (Matrix (Fin n) (Fin n) ℝ))) := hRat.symm
         _ ≤ span ℝ (unitriangularLieLatticeLogSet V hV) := ?_
    apply span_le.mpr
    intro X hX
    obtain ⟨A, hA⟩ := unitriangularLatticeRationalStructure_strict_preimage hX.2 (hV hX.1)
    obtain ⟨D, hD, hp⟩ := unitriangular_rational_exponential_lattice A
    let Y := strictUpperTriangularMap (algebraMap ℚ ℝ) A
    have hY : Y.val ∈ V := hA ▸ hX.1
    have he : unitriangularExponential ((D : ℝ) • Y) ∈ integerUnitriangularLattice n := by
      simpa only [Int.cast_one, mul_one] using hp 1
    have hv : unitriangularExponential ((D : ℝ) • Y) ∈ unitriangularLieSubgroup V hV := by
      change (unitriangularLogarithm (unitriangularExponential ((D : ℝ) • Y))).val ∈ V
      rw [unitriangularLogarithm_exponential]
      exact V.smul_mem _ hY
    have hm : (D : ℝ) • X ∈ span ℝ (unitriangularLieLatticeLogSet V hV) := by
      apply subset_span
      refine ⟨unitriangularExponential ((D : ℝ) • Y), ⟨hv, he⟩, ?_⟩
      change (unitriangularLogarithm (unitriangularExponential ((D : ℝ) • Y))).val = (D : ℝ) • X
      rw [unitriangularLogarithm_exponential]
      change (D : ℝ) • Y.val = (D : ℝ) • X
      rw [hA]
    exact (smul_mem_iff _ (by exact_mod_cast hD.ne' : (D : ℝ) ≠ 0)).mp hm

 theorem rationalUnitriangularLieSubalgebra_iff_lattice_log_span
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) :
    RationalUnitriangularLieSubalgebra V ↔
      span ℝ (unitriangularLieLatticeLogSet V hV) = V.toSubmodule := by
  constructor
  · exact rationalUnitriangularLieSubalgebra_lattice_log_span V hV
  · intro h
    apply le_antisymm
    · exact span_le.mpr fun _ hx => hx.1
    · calc V.toSubmodule = span ℝ (unitriangularLieLatticeLogSet V hV) := h.symm
           _ ≤ span ℝ ((V : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
             (unitriangularLatticeRationalStructure n : Set (Matrix (Fin n) (Fin n) ℝ))) := ?_
      apply span_mono
      rintro X ⟨g, hg, rfl⟩
      exact ⟨hg.1, subset_span ⟨g, hg.2, rfl⟩⟩

 theorem rationalUnitriangularLieSubalgebra_finite_lattice_log_generators
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    ∃ s : Finset (Matrix (Fin n) (Fin n) ℝ),
      (s : Set (Matrix (Fin n) (Fin n) ℝ)) ⊆ unitriangularLieLatticeLogSet V hV ∧
        span ℝ (s : Set (Matrix (Fin n) (Fin n) ℝ)) = V.toSubmodule := by
  have hs := rationalUnitriangularLieSubalgebra_lattice_log_span V hV hRat
  have hfg : (span ℝ (unitriangularLieLatticeLogSet V hV)).FG := by
    rw [hs]
    exact (Submodule.fg_iff_finiteDimensional V.toSubmodule).mpr inferInstance
  obtain ⟨s, hsub, heq⟩ :=
    (fg_span_iff_fg_span_finset_subset (unitriangularLieLatticeLogSet V hV)).mp hfg
  exact ⟨s, hsub, heq.symm.trans hs⟩

end Hindman168
