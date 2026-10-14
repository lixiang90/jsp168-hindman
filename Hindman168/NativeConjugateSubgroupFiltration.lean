import Hindman168.NativeRationalConjugateFiltration
import Hindman168.NativeRationalSubgroupFiltration

/-! Rational residue conjugation changes the specified lattice, while
retaining every layer of the SAME possibly proper subgroup filtration. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeConjugateSubgroupFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    NativeRationalSubgroupFiltration (nativeConjugateNilmanifoldData D ρ) ℓ := by
  have hv := (nativeSubgroupRationalHull_mem_iff (E := D.E) (I := D.I) D.Γ ρ).mp hρ
  have he := rough_native_conjugate_log_span (E := D.E) (I := D.I) (G := D.G) D.Γ hv
  rw [nativeLieExponential_globalLogarithm] at he
  exact {
    layer := F.layer
    antitone := F.antitone
    initial := F.initial
    bracket := F.bracket
    terminal := F.terminal
    rational := by
      intro i
      change Submodule.span ℝ (((F.layer i).restrictScalars ℚ ⊓
        nativeSubgroupRationalLogSpan (E := D.E) (I := D.I)
          (roughConjugateSubgroup D.Γ ρ) : Submodule ℚ D.E) : Set D.E) = F.layer i
      rw [he]
      exact F.rational i }

theorem native_conjugate_subgroup_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (i : ℕ) :
    (nativeConjugateSubgroupFiltration D F ρ hρ).layer i = F.layer i := rfl

theorem native_conjugate_subgroup_filtration_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (i : ℕ) :
    nativeRationalSubgroupLayer (nativeConjugateNilmanifoldData D ρ)
      (nativeConjugateSubgroupFiltration D F ρ hρ) i = nativeRationalSubgroupLayer D F i := rfl

end Hindman168
