import Hindman168.OriginalBoundedNativeModels
import OAI.Combinatorics.Progressions.Estimates.NativeModelOrbit

/-! A bounded rational signature determines a filtered Lie model and its
canonical grid cover, including every polynomial orbit and its actual observable. -/

namespace Hindman168.OriginalBoundedNativeModels

open Module OAI.Erdos3
open scoped TensorProduct NNReal

section Signatures

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def filteredGeometryCode : RationalModelCode s :=
  ⟨d, D.grid, D.rationalModelCoordinates⟩

theorem filteredGeometryCode_mem {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) :
    filteredGeometryCode D ∈
      boundedRationalModelCodes s ⌈p⌉₊ ⌈Real.exp p⌉₊ ⌈Real.exp p⌉₊ := by
  apply mem_boundedRationalModelCodes
  · exact Nat.cast_le.mp (hD.1.trans (Nat.le_ceil _))
  · exact Nat.cast_le.mp (hD.2.1.trans (Nat.le_ceil _))
  · intro k
    exact rationalHeight_of_logHeight (D.rationalModelCoordinates_height hp hD k)

end Signatures

section FilteredCover

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
  (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates) (hgrid : D.grid = E.grid)

include hgrid in
theorem rationalModelGroupEquiv_map_gridGeneratedLattice :
    (gridGeneratedLattice D).map (D.rationalModelGroupEquiv E h).toMonoidHom =
      gridGeneratedLattice E := by
  classical
  unfold gridGeneratedLattice
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change E.basis.equivFun (D.rationalModelGroupEquiv E h x).coord ∈
      scaledIntegerGrid E.grid
    rw [D.rationalModelGroupEquiv_coordinates E h, ← hgrid]
    exact hx
  · intro hg
    refine ⟨(D.rationalModelGroupEquiv E h).symm g, ?_,
      (D.rationalModelGroupEquiv E h).apply_symm_apply g⟩
    change D.basis.equivFun ((D.rationalModelGroupEquiv E h).symm g).coord ∈
      scaledIntegerGrid D.grid
    rw [← D.rationalModelGroupEquiv_coordinates E h,
      MulEquiv.apply_symm_apply, hgrid]
    exact hg

/-- Matching finite signatures identify the canonical grid covers as actual
filtered nilmanifolds, not merely as equal tables of structure constants. -/
noncomputable def filteredGridCoverEquiv :
    RationalFilteredNilmanifold.NativeModelEquiv (gridCover D) (gridCover E) where
  toLieEquiv := D.rationalModelEquiv E h
  map_basis := D.rationalModelEquiv_basis E h
  mem_layer n x := D.rationalModelGroupEquiv_mem_layer E h n ⟨x⟩
  mem_lattice g := by
    change D.rationalModelGroupEquiv E h g ∈ gridGeneratedLattice E ↔
      g ∈ gridGeneratedLattice D
    rw [← rationalModelGroupEquiv_map_gridGeneratedLattice D E h hgrid,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end FilteredCover

section Pullback

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d)

theorem gridCover_realLattice_le : (gridCover D).realLattice ≤ D.realLattice :=
  Subgroup.map_mono (gridGeneratedLattice_le D)

noncomputable def gridCoverProjection : (gridCover D).Space → D.Space :=
  cosetMap (gridCover D).realLattice D.realLattice (MonoidHom.id D.RealGroup)
    (gridCover_realLattice_le D)

@[simp] theorem gridCoverProjection_mk (g : D.RealGroup) :
    gridCoverProjection D (QuotientGroup.mk g) = QuotientGroup.mk g := rfl

/-- Passing to the smaller lattice is non-expanding for the specified
quotient metrics. -/
theorem gridCoverProjection_lipschitz :
    letI := (gridCover D).metricSpace
    letI := D.metricSpace
    LipschitzWith 1 (gridCoverProjection D) := by
  letI : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) :=
    (D.basis.baseChange ℝ).finiteDimensional_of_finite
  letI := NilpotentLieBCHGroup.rightMetricSpace
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  letI := NilpotentLieBCHGroup.rightMetricSpace_isIsometricSMul
    (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
  exact lipschitz_cosetMap (gridCover D).realLattice D.realLattice
    (gridCover D).realLattice_closed_discrete.1 D.realLattice_closed_discrete.1
    (MonoidHom.id D.RealGroup) (gridCover_realLattice_le D) LipschitzWith.id

variable {σ : Type*} {w : σ → ℕ}

noncomputable def gridCoverNiltest (T : D.Niltest w) : (gridCover D).Niltest w where
  orbit := T.orbit
  observable := T.observable ∘ gridCoverProjection D
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le x := T.norm_le _
  lipschitz := by
    letI := (gridCover D).metricSpace
    letI := D.metricSpace
    simpa only [mul_one] using T.lipschitz.comp (gridCoverProjection_lipschitz D)

@[simp] theorem gridCoverNiltest_eval (T : D.Niltest w) (x : σ → ℤ) :
    (gridCoverNiltest D T).eval x = T.eval x := rfl

@[simp] theorem gridCoverNiltest_normBound (T : D.Niltest w) :
    (gridCoverNiltest D T).normBound = T.normBound := rfl

@[simp] theorem gridCoverNiltest_lipBound (T : D.Niltest w) :
    (gridCoverNiltest D T).lipBound = T.lipBound := rfl

end Pullback

section PolynomialTransport

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
  (E : RationalFilteredNilmanifold M s d)
  (h : D.rationalModelCoordinates = E.rationalModelCoordinates) (hgrid : D.grid = E.grid)
  {σ : Type*} {w : σ → ℕ}

/-- Transport from an arbitrary lattice to the fixed representative's
canonical cover. All integer polynomial values are preserved exactly. -/
noncomputable def transportNiltest (T : D.Niltest w) : (gridCover E).Niltest w where
  orbit := (filteredGridCoverEquiv D E h hgrid).mapOrbit T.orbit
  observable := (gridCoverNiltest D T).observable ∘
    (filteredGridCoverEquiv D E h hgrid).symm.spaceMap
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le x := T.norm_le _
  lipschitz := by
    letI := (gridCover D).metricSpace
    letI := (gridCover E).metricSpace
    exact (gridCoverNiltest D T).lipschitz.comp
      (filteredGridCoverEquiv D E h hgrid).symm.spaceMap_lipschitz

theorem transportNiltest_eval (T : D.Niltest w) (x : σ → ℤ) :
    (transportNiltest D E h hgrid T).eval x = T.eval x := by
  let e := filteredGridCoverEquiv D E h hgrid
  change (gridCoverNiltest D T).observable (e.symm.spaceMap
    (QuotientGroup.mk ((gridCover E).filtration.realification.polynomialOrbitEval w x
      (e.mapOrbit T.orbit)))) = T.eval x
  rw [e.mapOrbit_eval, ← e.spaceMap_mk, e.symm_spaceMap_apply]
  rfl

@[simp] theorem transportNiltest_normBound (T : D.Niltest w) :
    (transportNiltest D E h hgrid T).normBound = T.normBound := rfl

@[simp] theorem transportNiltest_lipBound (T : D.Niltest w) :
    (transportNiltest D E h hgrid T).lipBound =
      T.lipBound * coordinateLipschitzBound d d 1 := rfl


/-- Every pointwise norm bound is preserved by the actual observable pullback. -/
theorem transportNiltest_norm_le (T : D.Niltest w) {B : ℝ}
    (hT : ∀ z, ‖T.observable z‖ ≤ B) (z : (gridCover E).Space) :
    ‖(transportNiltest D E h hgrid T).observable z‖ ≤ B :=
  hT _

end PolynomialTransport

end Hindman168.OriginalBoundedNativeModels
