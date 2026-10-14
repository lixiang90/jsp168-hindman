import Hindman168.AlignmentGradedLiePolynomialArrays
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Nilpotence bounds the actual polynomial degrees, hence the coefficient
array Lie algebra is finite dimensional for finitely many input variables. -/

namespace Hindman168
open scoped TensorProduct

section CommRing
variable (σ R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def alignmentBoundedLieArraySpace (s : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] L) :=
  ((MvPolynomial.restrictTotalDegree σ R s).subtype.rTensor L).range

variable {σ R L}

theorem alignmentLieArrayGenerator_highDegree_zero {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥)
    (d : σ →₀ ℕ) (x : L)
    (hx : x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1))
    (hd : s < d.sum (fun _ n => n)) :
    MvPolynomial.monomial d (1 : R) ⊗ₜ[R] x = 0 := by
  have hxs := LieModule.antitone_lowerCentralSeries R L L (by omega :
    s ≤ d.sum (fun _ n => n) - 1) hx
  rw [hs, LieSubmodule.mem_bot] at hxs
  rw [hxs, TensorProduct.tmul_zero]

theorem alignmentLieArraySpace_le_bounded {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    alignmentLieArraySpace σ R L ≤ alignmentBoundedLieArraySpace σ R L s := by
  apply Submodule.span_le.mpr
  rintro z ⟨d, x, hx, rfl⟩
  by_cases hd : d.sum (fun _ n => n) ≤ s
  · have hp : MvPolynomial.monomial d (1 : R) ∈
        MvPolynomial.restrictTotalDegree σ R s := by
      apply (MvPolynomial.mem_restrictTotalDegree σ s _).mpr
      exact (MvPolynomial.totalDegree_monomial_le d 1).trans hd
    exact ⟨⟨MvPolynomial.monomial d 1, hp⟩ ⊗ₜ[R] x, rfl⟩
  · rw [alignmentLieArrayGenerator_highDegree_zero hs d x hx (Nat.lt_of_not_ge hd)]
    exact Submodule.zero_mem _

theorem alignmentBoundedLieArraySpace_finite [Finite σ] [Module.Finite R L] (s : ℕ) :
    Module.Finite R (alignmentBoundedLieArraySpace σ R L s) := by
  unfold alignmentBoundedLieArraySpace
  infer_instance

end CommRing

variable {σ R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]

theorem alignmentLiePolynomialArrays_finiteDimensional [Finite σ]
    [FiniteDimensional R L] {s : ℕ}
    (hs : LieModule.lowerCentralSeries R L L s = ⊥) :
    FiniteDimensional R (alignmentLiePolynomialArrays σ R L) := by
  letI := alignmentBoundedLieArraySpace_finite (σ := σ) (R := R) (L := L) s
  exact Submodule.finiteDimensional_of_le (alignmentLieArraySpace_le_bounded hs)

end Hindman168
