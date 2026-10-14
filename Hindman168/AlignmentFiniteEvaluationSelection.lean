import Hindman168.AlignmentLieArrayIntegerSeparation
import Mathlib.RingTheory.Artinian.Module

/-! Finite-dimensional coefficient arrays can be determined by finitely
many actual integer evaluations. The finite selection uses minimality of
finite intersections of evaluation kernels in an Artinian module. -/

namespace Hindman168

theorem alignment_finite_linear_kernel_selection
    {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    (f : ι → V →ₗ[K] W)
    (hf : ∀ x : V, (∀ i, f i x = 0) → x = 0) :
    ∃ S : Finset ι, ∀ x : V, (∀ i ∈ S, f i x = 0) → x = 0 := by
  classical
  let P : Finset ι → Submodule K V := fun S => ⨅ i ∈ S, (f i).ker
  obtain ⟨Q, ⟨S, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal
    (Set.range P) ⟨P ∅, ⟨∅, rfl⟩⟩
  have hker : ∀ i, P S ≤ (f i).ker := by
    intro i
    have hle : P (insert i S) ≤ P S := by
      apply le_iInf
      intro j
      apply le_iInf
      intro hj
      exact iInf_le_of_le j (iInf_le _ (Finset.mem_insert_of_mem hj))
    have hreverse : P S ≤ P (insert i S) := by
      by_contra h
      exact hmin _ ⟨insert i S, rfl⟩ (lt_of_le_not_ge hle h)
    exact hreverse.trans (iInf_le_of_le i (iInf_le _ (Finset.mem_insert_self i S)))
  refine ⟨S, fun x hx => hf x fun i => ?_⟩
  apply LinearMap.mem_ker.mp
  apply hker i
  change x ∈ ⨅ j ∈ S, (f j).ker
  simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hx

variable {σ R L : Type*} [Field R] [CharZero R] [LieRing L] [LieAlgebra R L]

theorem alignmentLiePolynomialArrays_finite_integer_evaluations [Finite σ]
    [FiniteDimensional R L] {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    ∃ S : Finset (σ → ℤ), ∀ x : alignmentLiePolynomialArrays σ R L,
      (∀ u ∈ S, alignmentLiePolynomialArraysEvaluation (fun j => (u j : R)) x = 0) →
        x = 0 := by
  letI := alignmentLiePolynomialArrays_finiteDimensional (σ := σ) hs
  apply alignment_finite_linear_kernel_selection
    (fun u : σ → ℤ => (alignmentLiePolynomialArraysEvaluation
      (fun j => (u j : R))).toLinearMap)
  intro x hx
  apply Subtype.ext
  exact alignmentLieArray_zero_of_integer_evaluations (Module.Free.chooseBasis R L)
    x.val hx

end Hindman168
