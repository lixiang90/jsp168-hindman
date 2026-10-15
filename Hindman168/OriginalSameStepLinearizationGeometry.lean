import Hindman168.OriginalSameStepLinearizationGrid
import Hindman168.OriginalSameStepLinearizationReal
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

/-!
# A fixed same-step ambient rational nilmanifold

The ambient lattice and the positive integer clock period are chosen from
rational geometry alone.  The fibre lattice is the exact preimage of this
ambient lattice.  Its evaluation map lands in the original lattice, and
scalar extension preserves the exact preimage identity.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (hs : 1 ≤ s)

noncomputable def ambientBasis :
    Basis (Fin (finrank ℚ (Algebra D.filtration 1))) ℚ (Algebra D.filtration 1) := by
  letI := finiteDimensional_of_finite D.filtration 1
  exact Module.finBasis ℚ _

noncomputable def fiberBasis :
    Basis (Fin (finrank ℚ (Fiber D.filtration 1))) ℚ (Fiber D.filtration 1) := by
  letI := fiber_finiteDimensional D.filtration 1
  exact Module.finBasis ℚ _

/-- Evaluation at zero after the linear fibre projection. This need not be a
    Lie homomorphism on the whole extension, which is why grid clearing is
    formulated for linear maps. -/
noncomputable def ambientObservation : Algebra D.filtration 1 →ₗ[ℚ] L :=
  (fiberEvaluationLie D.filtration 1 0).toLinearMap.comp
    (LieAlgebra.SemiDirectSum.projl (action D.filtration 1))

noncomputable def unitTime : Algebra D.filtration 1 :=
  LieAlgebra.SemiDirectSum.inr (action D.filtration 1) (fun _ => 1)

structure FixedGridData where
  grid : ℕ
  clock : ℕ
  lattice : Subgroup (Group D.filtration hs 1)
  grid_pos : 0 < grid
  clock_pos : 0 < clock
  coordinates : bchSubgroupCoordinates (ambientBasis D) lattice = scaledIntegerGrid grid
  observation : ∀ g ∈ lattice,
    ambientObservation D g.coord ∈ coordinateGridModule D.basis D.grid
  clock_mem : (⟨(clock : ℚ) • unitTime D⟩ : Group D.filtration hs 1) ∈ lattice

/-- All choices here precede the choice of polynomial orbit. -/
noncomputable def fixedGridData : FixedGridData D hs :=
  Classical.choice (by
    obtain ⟨B, A, Γ, hB, hA, hΓ, hobs, htime⟩ :=
      exists_observed_grid_lattice (ambientBasis D) D.basis
        (lowerCentralSeries_eq_bot D.filtration hs 1) (ambientObservation D)
        D.grid D.grid_pos (unitTime D)
    exact ⟨⟨B, A, Γ, hB, hA, hΓ, hobs, htime⟩⟩)

private theorem integerGrid_subset_denominatorGrid {ι : Type*} (a b : ℕ) :
    (scaledIntegerGrid a : Set (ι → ℚ)) ⊆ denominatorGrid b := by
  rintro x ⟨z, rfl⟩
  exact ((show IntegralVector (fun i => (z i : ℚ)) from
    ⟨z, fun _ => rfl⟩).nat_smul a).nat_smul b

/-- The fixed ambient rational nilmanifold has the original step. -/
noncomputable def ambientModel :
    RationalFilteredNilmanifold (Algebra D.filtration 1) s
      (finrank ℚ (Algebra D.filtration 1)) := by
  letI := finiteDimensional_of_finite D.filtration 1
  exact {
    filtration := filtration D.filtration hs 1
    basis := ambientBasis D
    layerBasis := fun i => Module.finBasis ℚ _
    lattice := (fixedGridData D hs).lattice
    grid := (fixedGridData D hs).grid
    grid_pos := (fixedGridData D hs).grid_pos
    inner_grid := by rw [(fixedGridData D hs).coordinates]
    outer_grid := by
      rw [(fixedGridData D hs).coordinates]
      exact integerGrid_subset_denominatorGrid _ _ }

noncomputable def ambientFiberInclusion :
    FiberGroup D.filtration 1 →* (ambientModel D hs).filtration.Group :=
  NilpotentLieBCHGroup.map (LieAlgebra.SemiDirectSum.inl (action D.filtration 1))

noncomputable def fiberLattice : Subgroup (FiberGroup D.filtration 1) :=
  (ambientModel D hs).lattice.comap (ambientFiberInclusion D hs)

theorem fiberLattice_grid :
    ∃ N : ℕ, 0 < N ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates (fiberBasis D) (fiberLattice D hs) ∧
      bchSubgroupCoordinates (fiberBasis D) (fiberLattice D hs) ⊆ denominatorGrid N :=
  exists_bchSubgroup_comap_grid (fiberBasis D) (ambientBasis D)
    (LieAlgebra.SemiDirectSum.inl (action D.filtration 1))
    (LieAlgebra.SemiDirectSum.inl_injective (action D.filtration 1))
    (ambientModel D hs).lattice (ambientModel D hs).grid (ambientModel D hs).grid_pos
    (ambientModel D hs).inner_grid (ambientModel D hs).outer_grid

/-- The time-zero fibre with precisely the induced lattice. -/
noncomputable def fiberModel :
    RationalFilteredNilmanifold (Fiber D.filtration 1) s
      (finrank ℚ (Fiber D.filtration 1)) := by
  letI := fiber_finiteDimensional D.filtration 1
  exact {
    filtration := fiberFiltration D.filtration 1
    basis := fiberBasis D
    layerBasis := fun i => Module.finBasis ℚ _
    lattice := fiberLattice D hs
    grid := (fiberLattice_grid D hs).choose
    grid_pos := (fiberLattice_grid D hs).choose_spec.1
    inner_grid := (fiberLattice_grid D hs).choose_spec.2.1
    outer_grid := (fiberLattice_grid D hs).choose_spec.2.2 }

/-- The observer is well-defined on the fibre quotient. -/
theorem fiberEvaluation_lattice :
    (fiberModel D hs).lattice ≤ D.lattice.comap (fiberEvaluation D.filtration 1 0) := by
  intro g hg
  apply (bchSubgroupCoordinates_repr D.basis D.lattice _).mp
  apply D.inner_grid
  exact (fixedGridData D hs).observation (ambientFiberInclusion D hs g) hg

noncomputable def modelFiberInclusion :
    (fiberModel D hs).RealGroup →* (ambientModel D hs).RealGroup :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (fiberModel D hs).filtration.lowerCentralSeries_eq_bot)
    (hM := (ambientModel D hs).filtration.lowerCentralSeries_eq_bot)
    (LieAlgebra.SemiDirectSum.inl (action D.filtration 1))

/-- The induced real lattice has no additional elements: the fibre quotient
    therefore injects into the ambient quotient. -/
theorem fiberRealLattice_eq_comap :
    (fiberModel D hs).realLattice =
      (ambientModel D hs).realLattice.comap (modelFiberInclusion D hs) :=
  realification_comap_of_leftInverse (ambientBasis D)
    (LieAlgebra.SemiDirectSum.inl (action D.filtration 1))
    (LieAlgebra.SemiDirectSum.projl (action D.filtration 1))
    (fun _ => rfl) (ambientModel D hs).lattice

/-- Every integer clock correction is a genuine ambient lattice element. -/
theorem clock_zpow_mem (n : ℤ) :
    (⟨((fixedGridData D hs).clock : ℚ) • unitTime D⟩ :
      (ambientModel D hs).filtration.Group) ^ n ∈ (ambientModel D hs).lattice :=
  (ambientModel D hs).lattice.zpow_mem (fixedGridData D hs).clock_mem n

end Hindman168.OriginalSameStepLinearization
