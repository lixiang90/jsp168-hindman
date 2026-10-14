import Hindman168.AlignmentLieLowerCentralBrackets
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.MvPolynomial.Basic

/-! The coefficient Lie algebra of the paper's polynomial arrays: a monomial
of positive degree d has its coefficient in lower-central layer d-1.
Degree zero has an unrestricted coefficient. -/

namespace Hindman168
open scoped TensorProduct

variable (σ R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

def alignmentLieArrayGenerators : Set (MvPolynomial σ R ⊗[R] L) :=
  {z | ∃ (d : σ →₀ ℕ) (x : L),
    x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1) ∧
    z = MvPolynomial.monomial d 1 ⊗ₜ[R] x}

noncomputable def alignmentLieArraySpace : Submodule R (MvPolynomial σ R ⊗[R] L) :=
  Submodule.span R (alignmentLieArrayGenerators σ R L)

variable {σ R L}

theorem alignmentLieArrayGenerators_bracket {x y : MvPolynomial σ R ⊗[R] L}
    (hx : x ∈ alignmentLieArrayGenerators σ R L)
    (hy : y ∈ alignmentLieArrayGenerators σ R L) :
    ⁅x, y⁆ ∈ alignmentLieArrayGenerators σ R L := by
  obtain ⟨d, a, ha, rfl⟩ := hx
  obtain ⟨e, b, hb, rfl⟩ := hy
  refine ⟨d + e, ⁅a, b⁆, ?_, ?_⟩
  · rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    exact alignmentLie_weighted_lowerCentral_bracket ha hb
  · rw [LieAlgebra.ExtendScalars.bracket_tmul, MvPolynomial.monomial_mul,
    one_mul]

theorem alignmentLieArraySpace_bracket {x y : MvPolynomial σ R ⊗[R] L}
    (hx : x ∈ alignmentLieArraySpace σ R L)
    (hy : y ∈ alignmentLieArraySpace σ R L) :
    ⁅x, y⁆ ∈ alignmentLieArraySpace σ R L := by
  refine Submodule.span_induction₂
    (p := fun x y _ _ => ⁅x, y⁆ ∈ alignmentLieArraySpace σ R L)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    exact Submodule.subset_span (alignmentLieArrayGenerators_bracket hx hy)
  · intro y _
    rw [zero_lie y]
    exact Submodule.zero_mem _
  · intro x _
    rw [lie_zero x]
    exact Submodule.zero_mem _
  · intro x y z _ _ _ hx hy
    rw [add_lie x y z]
    exact Submodule.add_mem _ hx hy
  · intro x y z _ _ _ hx hy
    rw [lie_add x y z]
    exact Submodule.add_mem _ hx hy
  · intro r x y _ _ h
    rw [smul_lie r x y]
    exact Submodule.smul_mem _ r h
  · intro r x y _ _ h
    rw [lie_smul r x y]
    exact Submodule.smul_mem _ r h

variable (σ R L) in
noncomputable def alignmentLiePolynomialArrays : LieSubalgebra R (MvPolynomial σ R ⊗[R] L) where
  __ := alignmentLieArraySpace σ R L
  lie_mem' := alignmentLieArraySpace_bracket

theorem alignmentLiePolynomialArrays_monomial (d : σ →₀ ℕ) (x : L)
    (hx : x ∈ LieModule.lowerCentralSeries R L L (d.sum (fun _ n => n) - 1)) :
    MvPolynomial.monomial d 1 ⊗ₜ[R] x ∈ alignmentLiePolynomialArrays σ R L :=
  Submodule.subset_span ⟨d, x, hx, rfl⟩

end Hindman168
