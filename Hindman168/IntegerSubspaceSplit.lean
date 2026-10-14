import Hindman168.IntegerSubspaceQuotient
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Prod

/-! The actual integer intersection with any real subspace admits an
integer direct complement in any finitely generated integer module.
No rational vector-space complement is substituted for this integer one. -/

namespace Hindman168

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (L : Submodule ℤ E) (V : Submodule ℝ E) [Module.Finite ℤ L]

theorem integer_subspace_quotient_section_exists :
    ∃ s : (L ⧸ integerSubspaceIntersection L V) →ₗ[ℤ] L,
      ((integerSubspaceIntersection L V).mkQ.restrictScalars ℤ).comp s = LinearMap.id := by
  letI : Module.Free ℤ (L ⧸ integerSubspaceIntersection L V) :=
    integer_subspace_quotient_free L V
  letI : Module.Projective ℤ (L ⧸ integerSubspaceIntersection L V) :=
    Module.Projective.of_free
  exact ((integerSubspaceIntersection L V).mkQ.restrictScalars ℤ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (integerSubspaceIntersection L V).mkQ_surjective)

theorem integer_subspace_integer_complement_exists :
    ∃ Q : Submodule ℤ L, IsCompl (integerSubspaceIntersection L V) Q := by
  let P := integerSubspaceIntersection L V
  obtain ⟨s, hs⟩ := integer_subspace_quotient_section_exists L V
  have hright : ∀ x, P.mkQ (s x) = x :=
    fun x => congrArg (fun f : (L ⧸ P) →ₗ[ℤ] (L ⧸ P) => f x) hs
  refine ⟨s.range, ?_⟩
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hp
    obtain ⟨y, hy⟩ := hp
    have hz : P.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hx
    rw [← hy, hright] at hz
    rw [← hy, hz, map_zero]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    refine ⟨x-s (P.mkQ x), ?_, s (P.mkQ x), ⟨P.mkQ x, rfl⟩, sub_add_cancel _ _⟩
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (x-s (P.mkQ x)) = 0
    rw [map_sub, hright, sub_self]

end Hindman168
