import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Finiteness.Basic

/-! The quotient of an actual integer module in a real vector space by
its intersection with a real subspace embeds in the real quotient. Thus
the integer quotient is torsion-free and is free when finitely generated.
This statement applies to the genuine central logarithmic lattice. -/

namespace Hindman168

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  (L : Submodule ℤ E) (V : Submodule ℝ E)

def integerSubspaceIntersection : Submodule ℤ L :=
  (V.restrictScalars ℤ).comap L.subtype

noncomputable def integerSubspaceQuotientEmbedding :
    (L ⧸ integerSubspaceIntersection L V) →ₗ[ℤ] (E ⧸ V) :=
  (integerSubspaceIntersection L V).liftQ
    ((V.mkQ.restrictScalars ℤ).comp L.subtype)
      (by intro x hx; exact (Submodule.Quotient.mk_eq_zero V).mpr hx)

theorem integer_subspace_quotient_embedding_mk (x : L) :
    integerSubspaceQuotientEmbedding L V ((integerSubspaceIntersection L V).mkQ x) =
      V.mkQ (x : E) := rfl

theorem integer_subspace_quotient_embedding_injective :
    Function.Injective (integerSubspaceQuotientEmbedding L V) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨x, rfl⟩ := (integerSubspaceIntersection L V).mkQ_surjective q
  apply (Submodule.Quotient.mk_eq_zero (integerSubspaceIntersection L V)).mpr
  change V.mkQ (x : E) = 0 at hq
  exact (Submodule.Quotient.mk_eq_zero V).mp hq

theorem integer_subspace_quotient_torsionFree :
    Module.IsTorsionFree ℤ (L ⧸ integerSubspaceIntersection L V) := by
  letI : Module.IsTorsionFree ℤ (E ⧸ V) := Module.IsTorsionFree.trans ℝ
  exact (integer_subspace_quotient_embedding_injective L V).moduleIsTorsionFree
    (integerSubspaceQuotientEmbedding L V) (fun n x => map_smul _ n x)

theorem integer_subspace_quotient_free [Module.Finite ℤ L] :
    Module.Free ℤ (L ⧸ integerSubspaceIntersection L V) := by
  letI : Module.Finite ℤ (L ⧸ integerSubspaceIntersection L V) :=
    Module.Finite.of_surjective (integerSubspaceIntersection L V).mkQ
      (integerSubspaceIntersection L V).mkQ_surjective
  letI := integer_subspace_quotient_torsionFree L V
  exact Module.free_of_finite_type_torsion_free'

end Hindman168
