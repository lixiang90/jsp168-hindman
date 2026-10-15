import OAI.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry

/-!
# Fixed rational grids for a same-step shift extension

These lemmas use the BCH grid and realification constructions from OpenAI's
fixed `adc7f1241b42e322a6451854ab7e4b4c146bf78a` source.  They add denominator
clearing for an arbitrary linear observation and an exact realification/comap
identity for a split rational embedding.  No bounds depend on a polynomial
orbit or any of its coefficients.
-/

namespace Hindman168.OriginalSameStepLinearization

open OAI.Erdos3 Module
open scoped TensorProduct

section Grids

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

/-- Clearing the matrix denominators of a linear map sends a fixed coordinate
    grid into any prescribed target coordinate grid. -/
theorem linearMap_coordinateGrid (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (l : ℕ) {x : L}
    (hx : x ∈ coordinateGridModule e (rationalSpanGridStep f (fun i => φ (e i)) l)) :
    φ x ∈ coordinateGridModule f l := by
  classical
  obtain ⟨z, hz⟩ := hx
  have hcoeff (i : ι) : e.repr x i =
      (rationalSpanGridStep f (fun i => φ (e i)) l : ℚ) * (z i : ℚ) :=
    congrFun hz i
  rw [mem_coordinateGridModule, ← e.sum_repr x, map_sum]
  simpa only [map_smul, hcoeff, mul_comm] using
    rationalSpanGridStep_combination f (fun i => φ (e i)) l z

/-- A fixed rational vector has a positive integer multiple in every positive
    coordinate grid. -/
theorem exists_pos_smul_mem_coordinateGrid (e : Basis ι ℚ L) (B : ℕ)
    (hB : 0 < B) (x : L) :
    ∃ A : ℕ, 0 < A ∧ (A : ℚ) • x ∈ coordinateGridModule e B := by
  let v : Fin 1 → L := fun _ => x
  refine ⟨rationalSpanGridStep e v B, rationalSpanGridStep_pos e v B hB, ?_⟩
  simpa only [Fin.sum_univ_one, Int.cast_one, one_mul, v, mem_coordinateGridModule] using
    rationalSpanGridStep_combination e v B (fun _ => 1)

/-- Finite rational structure constants always have a common height bound. -/
theorem exists_structureHeight (e : Basis ι ℚ L) :
    ∃ H : ℕ, ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H := by
  classical
  let a : ι × ι × ι → ℕ := fun z =>
    max (lieStructureConstants e z.1 z.2.1 z.2.2).num.natAbs
      (lieStructureConstants e z.1 z.2.1 z.2.2).den
  refine ⟨Finset.univ.sup a, fun i j k => ?_⟩
  have h : a (i, j, k) ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ _)
  exact ⟨(Nat.le_max_left _ _).trans h, (Nat.le_max_right _ _).trans h⟩

/-- A genuine BCH-stable lattice can be chosen fine enough for a prescribed
    rational linear observation, and to contain a positive integer time step. -/
theorem exists_observed_grid_lattice (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (φ : L →ₗ[ℚ] M) (l : ℕ) (hl : 0 < l) (time : L) :
    ∃ (B A : ℕ) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)),
      0 < B ∧ 0 < A ∧
      bchSubgroupCoordinates e Γ = scaledIntegerGrid B ∧
      (∀ g ∈ Γ, φ g.coord ∈ coordinateGridModule f l) ∧
      (⟨(A : ℚ) • time⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
  let l' := rationalSpanGridStep f (fun i => φ (e i)) l
  have hl' : 0 < l' := rationalSpanGridStep_pos f _ l hl
  obtain ⟨H, hc⟩ := exists_structureHeight e
  obtain ⟨B, hB, hdiv, _, hstable⟩ := exists_bch_stable_integral_grid e hnil l' hl' hc
  let Γ := coordinateGridBCHSubgroup e B hnil hstable
  obtain ⟨A, hA, htime⟩ := exists_pos_smul_mem_coordinateGrid e B hB time
  refine ⟨B, A, Γ, hB, hA, coordinateGridBCHSubgroup_coordinates e B hnil hstable,
    ?_, htime⟩
  intro g hg
  apply linearMap_coordinateGrid e f φ l
  exact scaledIntegerGrid_subset_of_dvd hdiv hg

end Grids

section Realification

variable {ι L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]

/-- Scalar extension preserves an explicitly split rational linear inclusion. -/
theorem realification_leftInverse (φ : L →ₗ⁅ℚ⁆ M) (ψ : M →ₗ[ℚ] L)
    (hψ : Function.LeftInverse ψ φ) :
    Function.LeftInverse (ψ.baseChange ℝ) (realificationLieHom φ) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp only [realificationLieHom_tmul, LinearMap.baseChange_tmul, hψ x]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The rational preimage lattice becomes exactly the real preimage lattice.
    This is stronger than the usual functorial containment and is what ensures
    that the fibre quotient injects into the ambient quotient. -/
theorem realification_comap_of_leftInverse (e : Basis ι ℚ M)
    {s t : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (ψ : M →ₗ[ℚ] L) (hψ : Function.LeftInverse ψ φ)
    (Γ : Subgroup (NilpotentLieBCHGroup M t hM)) :
    (Γ.comap (NilpotentLieBCHGroup.mapOfSteps (hL := hL) φ)).map
        NilpotentLieBCHGroup.realificationHom =
      (Γ.map NilpotentLieBCHGroup.realificationHom).comap
        (NilpotentLieBCHGroup.realificationMap (hnil := hL) (hM := hM) φ) := by
  apply le_antisymm
  · exact NilpotentLieBCHGroup.realificationMap_subgroup φ _ Γ le_rfl
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
    let q : NilpotentLieBCHGroup L s hL := ⟨ψ y.coord⟩
    have hq : NilpotentLieBCHGroup.realificationHom q = x := by
      apply NilpotentLieBCHGroup.ext
      have h := congrArg (fun g => ψ.baseChange ℝ g.coord) hxy
      simpa only [NilpotentLieBCHGroup.realificationHom_coord,
        NilpotentLieBCHGroup.realificationMap_coord, rationalLieInclusion_apply,
        LinearMap.baseChange_tmul, realification_leftInverse φ ψ hψ x.coord] using h
    have hmap : NilpotentLieBCHGroup.mapOfSteps (hM := hM) φ q = y := by
      apply NilpotentLieBCHGroup.realificationHom_injective e
      rw [← NilpotentLieBCHGroup.realificationMap_realificationHom_ofSteps, hq]
      exact hxy.symm
    exact Subgroup.mem_map.mpr ⟨q, by simpa only [Subgroup.mem_comap, hmap] using hy, hq⟩

end Realification

end Hindman168.OriginalSameStepLinearization
