import Hindman168.NativeRationalConjugateFiltration
import Hindman168.NativeRationalWeightedOperations

/-! EVERY actual finite rational representative receives TRUE conjugated
native data and the SAME smaller rational Lie layers. Actual source weights
and strict nonlinearity drop survive; no child correlation is supplied. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_residue_direction_mem_span {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (y : D.E)
    (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (M m : ℕ) :
    ((m : ℝ)/(M : ℝ)) • y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ := by
  have he := Rat.cast_smul_eq_qsmul ℝ ((m : ℚ)/(M : ℚ)) y
  push_cast at he
  rw [he]
  exact (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ).smul_mem _ hy

noncomputable def nativeRationalResidueFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K : NativeRationalLieFiltration D ℓ) (y : D.E)
    (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (M m : ℕ) :
    NativeRationalLieFiltration
      (nativeConjugateNilmanifoldData D
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (((m : ℝ)/(M : ℝ)) • y))) ℓ :=
  nativeRationalConjugateFiltration D K (((m : ℝ)/(M : ℝ)) • y)
    (native_rational_residue_direction_mem_span D y hy M m)

theorem native_rational_residue_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K : NativeRationalLieFiltration D ℓ) (y : D.E)
    (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (M m i : ℕ) :
    (nativeRationalResidueFiltration D K y hy M m).layer i=K.layer i := rfl

theorem native_rational_residue_filtration_weighted {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (K : NativeRationalLieFiltration D ℓ) (y : D.E)
    (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (M m : ℕ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree K.layer p 0) :
    RoughVectorMvWeightedDegree (nativeRationalResidueFiltration D K y hy M m).layer p 0 := hp

theorem native_rational_residue_filtration_nonlinearity_lt {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L K : NativeRationalLieFiltration D ℓ)
    (hDrop : nativeRationalFiltrationNonlinearity D K < nativeRationalFiltrationNonlinearity D L)
    (y : D.E) (hy : y ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (M m : ℕ) :
    nativeRationalFiltrationNonlinearity _ (nativeRationalResidueFiltration D K y hy M m) <
      nativeRationalFiltrationNonlinearity D L := hDrop

end Hindman168
