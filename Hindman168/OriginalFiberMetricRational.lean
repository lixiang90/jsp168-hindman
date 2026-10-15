import Hindman168.OriginalFiberMetricBCH
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

/-! The fixed-model interface for the same-step fibre inclusion. -/

namespace Hindman168.OriginalFiberMetric

open Module OAI.Erdos3 OAI.Erdos3.NilpotentLieBCHGroup
open scoped NNReal TensorProduct BigOperators

private theorem finite_rational_height_bound {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ H : ℕ, ∀ i, RationalHeightLE (q i) H := by
  classical
  refine ⟨Finset.univ.sup (fun i => max (q i).num.natAbs (q i).den), ?_⟩
  intro i
  have hi := Finset.le_sup (f := fun i => max (q i).num.natAbs (q i).den)
    (Finset.mem_univ i)
  exact ⟨(le_max_left _ _).trans hi, (le_max_right _ _).trans hi⟩

theorem exists_rationalCosetMap_antilipschitz
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M) (ψ : M →ₗ[ℚ] L) (hψ : ∀ x, ψ (φ x) = x)
    (hΓ : D.realLattice = E.realLattice.comap
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ)) :
    letI := D.metricSpace
    letI := E.metricSpace
    ∃ C : ℝ≥0, AntilipschitzWith C
      (cosetMap D.realLattice E.realLattice (realificationMap φ) hΓ.le) := by
  classical
  obtain ⟨HD, hHD⟩ := finite_rational_height_bound
    (fun p : Fin d × Fin d × Fin d => lieStructureConstants D.basis p.1 p.2.1 p.2.2)
  obtain ⟨HE, hHE⟩ := finite_rational_height_bound
    (fun p : Fin e × Fin e × Fin e => lieStructureConstants E.basis p.1 p.2.1 p.2.2)
  have hψR : ∀ x, ψ.baseChange ℝ (realificationLieHom φ x) = x := by
    have hcomp : ψ.comp φ.toLinearMap = LinearMap.id := by
      ext x
      exact hψ x
    have hbase := congrArg (fun f : L →ₗ[ℚ] L => f.baseChange ℝ) hcomp
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hbase
    intro x
    exact congrArg (fun f : (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L) => f x) hbase
  exact exists_cosetMap_antilipschitz
    (D.basis.baseChange ℝ) (E.basis.baseChange ℝ)
    (lieStructureConstants D.basis) (lieStructureConstants E.basis)
    (fun i j k => (realLieBasis_structure D.basis i j k).symm)
    (fun i j k => (realLieBasis_structure E.basis i j k).symm)
    (fun i j k => hHD (i, j, k)) (fun i j k => hHE (i, j, k))
    D.realLattice E.realLattice D.realLattice_closed_discrete.1 E.realLattice_closed_discrete.1
    E.grid E.grid_pos (realification_subgroup_grid E.basis E.lattice E.grid E.outer_grid)
    (realificationLieHom φ) (ψ.baseChange ℝ) hψR hΓ D.space_compact

end Hindman168.OriginalFiberMetric
