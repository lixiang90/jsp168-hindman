import Hindman168.NativeConjugateNilmanifoldData
import Hindman168.NativeRationalNonlinearKernelFiltration
import Hindman168.RoughNativeConjugateLogSpan

/-! ACTUAL rational conjugation preserves the TRUE rational log span.
Every actual original rational Lie filtration therefore transports to
the SAME layers on TRUE conjugated native data, preserving nonlinearity. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalConjugateFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    NativeRationalLieFiltration
      (nativeConjugateNilmanifoldData D (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)) ℓ := by
  have he := rough_native_conjugate_log_span (E := D.E) (I := D.I) (G := D.G) D.Γ hv
  exact {
    layer := L.layer
    antitone := L.antitone
    zero := L.zero
    one := L.one
    bracket := L.bracket
    terminal := L.terminal
    rational := by
      intro i
      change Submodule.span ℝ (((L.layer i).restrictScalars ℚ ⊓
        nativeSubgroupRationalLogSpan (E := D.E) (I := D.I)
          (roughConjugateSubgroup D.Γ (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)) :
            Submodule ℚ D.E) : Set D.E)=L.layer i
      rw [he]
      exact L.rational i }

theorem native_rational_conjugate_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) (i : ℕ) :
    (nativeRationalConjugateFiltration D L v hv).layer i=L.layer i := rfl

theorem native_rational_conjugate_filtration_nonlinearity {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (v : D.E) (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    nativeRationalFiltrationNonlinearity _ (nativeRationalConjugateFiltration D L v hv)=
      nativeRationalFiltrationNonlinearity D L := rfl

end Hindman168
