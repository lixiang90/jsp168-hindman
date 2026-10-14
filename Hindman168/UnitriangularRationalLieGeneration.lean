import Hindman168.UnitriangularRationalLieLatticeCompact
import Mathlib.Algebra.Module.Submodule.Bilinear

/-! Rational Lie generation inside the actual strict matrix algebra.
Real scalar extension of a rational Lie subalgebra is proved closed under
brackets by the actual bilinear map and its two-variable span identity. Real Lie generation then equals
that extension of rational Lie generation. The original integer lattice
rational-log structure is proved bracket closed using actual rational
matrix preimages, so every Lie span of its vectors is rational. -/

noncomputable section
namespace Hindman168
open Matrix Submodule Set

variable {n : ℕ}
local instance rationalGenerationMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing
local instance rationalGenerationEndLieRing :
    LieRing (Module.End ℝ (Matrix (Fin n) (Fin n) ℝ)) := LieRing.ofAssociativeRing
local instance rationalGenerationRatMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℚ) :=
  LieRing.ofAssociativeRing

 theorem unitriangularLatticeRationalStructure_lie_mem
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ unitriangularLatticeRationalStructure n)
    (hY : Y ∈ unitriangularLatticeRationalStructure n) :
    ⁅X, Y⁆ ∈ unitriangularLatticeRationalStructure n := by
  obtain ⟨A, rfl⟩ := (unitriangularLatticeRationalStructure_mem_iff X).mp hX
  obtain ⟨B, rfl⟩ := (unitriangularLatticeRationalStructure_mem_iff Y).mp hY
  let C : StrictUpperTriangular n ℚ := ⟨⁅A.val, B.val⁆,
    (A.property.lie B.property).antitone (by omega)⟩
  apply (unitriangularLatticeRationalStructure_mem_iff _).mpr
  refine ⟨C, ?_⟩
  change (algebraMap ℚ ℝ).mapMatrix (A.val * B.val - B.val * A.val) =
    (algebraMap ℚ ℝ).mapMatrix A.val * (algebraMap ℚ ℝ).mapMatrix B.val -
      (algebraMap ℚ ℝ).mapMatrix B.val * (algebraMap ℚ ℝ).mapMatrix A.val
  rw [map_sub, map_mul, map_mul]

 def unitriangularLatticeRationalLieSubalgebra (n : ℕ) :
    LieSubalgebra ℚ (Matrix (Fin n) (Fin n) ℝ) where
  toSubmodule := unitriangularLatticeRationalStructure n
  lie_mem' := unitriangularLatticeRationalStructure_lie_mem

 def realMatrixLieRestrictRat (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    LieSubalgebra ℚ (Matrix (Fin n) (Fin n) ℝ) where
  toSubmodule := V.toSubmodule.restrictScalars ℚ
  lie_mem' := V.lie_mem

 theorem rationalMatrixLie_real_span_lie_mem
    (U : LieSubalgebra ℚ (Matrix (Fin n) (Fin n) ℝ))
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ span ℝ (U : Set _)) (hY : Y ∈ span ℝ (U : Set _)) :
    ⁅X, Y⁆ ∈ span ℝ (U : Set _) := by
  let f := (LieAlgebra.ad ℝ (Matrix (Fin n) (Fin n) ℝ)).toLinearMap
  have hle : map₂ f (span ℝ (U : Set _)) (span ℝ (U : Set _)) ≤ span ℝ (U : Set _) := by
    rw [map₂_span_span]
    apply span_le.mpr
    rintro Z ⟨X, hX, Y, hY, rfl⟩
    exact subset_span (U.lie_mem hX hY)
  exact hle (apply_mem_map₂ f hX hY)

 def rationalMatrixLieRealExtension
    (U : LieSubalgebra ℚ (Matrix (Fin n) (Fin n) ℝ)) :
    LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toSubmodule := span ℝ (U : Set _)
  lie_mem' := rationalMatrixLie_real_span_lie_mem U

 theorem realMatrixLieSpan_eq_rational_extension (s : Set (Matrix (Fin n) (Fin n) ℝ)) :
    LieSubalgebra.lieSpan ℝ _ s =
      rationalMatrixLieRealExtension (LieSubalgebra.lieSpan ℚ _ s) := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    intro X hX
    exact subset_span (LieSubalgebra.subset_lieSpan hX)
  · have hq : LieSubalgebra.lieSpan ℚ _ s ≤
        realMatrixLieRestrictRat (LieSubalgebra.lieSpan ℝ _ s) :=
      LieSubalgebra.lieSpan_le.mpr (fun X hX => LieSubalgebra.subset_lieSpan hX)
    change span ℝ (LieSubalgebra.lieSpan ℚ _ s : Set _) ≤
      (LieSubalgebra.lieSpan ℝ _ s).toSubmodule
    exact span_le.mpr (fun X hX => hq hX)

 theorem rationalUnitriangularLieSubalgebra_lieSpan
    (s : Set (Matrix (Fin n) (Fin n) ℝ))
    (hs : s ⊆ (unitriangularLatticeRationalStructure n : Set _)) :
    RationalUnitriangularLieSubalgebra (LieSubalgebra.lieSpan ℝ _ s) := by
  have hq : LieSubalgebra.lieSpan ℚ _ s ≤ unitriangularLatticeRationalLieSubalgebra n :=
    LieSubalgebra.lieSpan_le.mpr hs
  rw [realMatrixLieSpan_eq_rational_extension]
  change span ℝ (((span ℝ (LieSubalgebra.lieSpan ℚ (Matrix (Fin n) (Fin n) ℝ) s :
      Set (Matrix (Fin n) (Fin n) ℝ))) : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
    (unitriangularLatticeRationalStructure n : Set (Matrix (Fin n) (Fin n) ℝ))) =
    span ℝ (LieSubalgebra.lieSpan ℚ (Matrix (Fin n) (Fin n) ℝ) s : Set (Matrix (Fin n) (Fin n) ℝ))
  apply le_antisymm
  · exact span_le.mpr (fun X hX => hX.1)
  · apply span_le.mpr
    intro X hX
    exact subset_span ⟨subset_span hX, hq hX⟩

 theorem unitriangularRationalLieSpan_le_strict
    (s : Set (Matrix (Fin n) (Fin n) ℝ))
    (hs : s ⊆ (unitriangularLatticeRationalStructure n : Set _)) :
    LieSubalgebra.lieSpan ℝ _ s ≤ strictUpperTriangularLieSubalgebra n ℝ :=
  LieSubalgebra.lieSpan_le.mpr (fun _ hX => unitriangularLatticeRationalStructure_strict (hs hX))

 theorem unitriangularRationalLieSpan_lattice_quotient_compact
    (s : Set (Matrix (Fin n) (Fin n) ℝ))
    (hs : s ⊆ (unitriangularLatticeRationalStructure n : Set _)) :
    CompactSpace (unitriangularLieSubgroup (LieSubalgebra.lieSpan ℝ _ s)
        (unitriangularRationalLieSpan_le_strict s hs) ⧸
      integerUnitriangularLieLattice (LieSubalgebra.lieSpan ℝ _ s)
        (unitriangularRationalLieSpan_le_strict s hs)) :=
  rationalUnitriangularLieLattice_quotient_compact _
    (unitriangularRationalLieSpan_le_strict s hs) (rationalUnitriangularLieSubalgebra_lieSpan s hs)

 theorem unitriangularRationalLieSpan_lattice_orbit_isCompact
    (s : Set (Matrix (Fin n) (Fin n) ℝ))
    (hs : s ⊆ (unitriangularLatticeRationalStructure n : Set _)) :
    IsCompact (((↑) : Unitriangular n ℝ → Unitriangular n ℝ ⧸ integerUnitriangularLattice n) ''
      (unitriangularLieSubgroup (LieSubalgebra.lieSpan ℝ _ s)
        (unitriangularRationalLieSpan_le_strict s hs) : Set (Unitriangular n ℝ))) :=
  rationalUnitriangularLieLattice_orbit_isCompact _
    (unitriangularRationalLieSpan_le_strict s hs) (rationalUnitriangularLieSubalgebra_lieSpan s hs)

end Hindman168
