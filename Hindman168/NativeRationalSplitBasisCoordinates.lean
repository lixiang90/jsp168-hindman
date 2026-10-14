import Hindman168.NativeRationalFirstLayerBasis
import Hindman168.RationalSubspaceFunctional

/-! EVERY real split-basis coordinate is the cast of the corresponding
actual rational coordinate on the true original rational log span. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_split_basis_coordinate_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (j : NativeRationalFirstLayerBasisIndex D L)
    (w : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    (nativeRationalFirstLayerRealBasis D L).repr w j =
      ((nativeRationalFirstLayerRationalBasis D L).repr w j : ℝ) := by
  letI := nativeLatticeRationalLogSpan_finiteDimensional (E := D.E) (I := D.I) D.Γ
  let f := rationalSubspaceFunctional _ (nativeLattice_rationalLogSpan_finrank (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan_real_span_eq_top (E := D.E) (I := D.I) D.Γ)
    ((nativeRationalFirstLayerRationalBasis D L).coord j)
  have hf (v : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
      f v = ((nativeRationalFirstLayerRationalBasis D L).coord j v : ℝ) :=
    rationalSubspaceFunctional_apply _ _ _ _ v
  have hcoord : f = (nativeRationalFirstLayerRealBasis D L).coord j := by
    apply (nativeRationalFirstLayerRealBasis D L).ext
    intro k
    have hk : f (nativeRationalFirstLayerRealBasis D L k) = if k=j then 1 else 0 := by
      rw [native_rational_first_layer_basis_apply,hf,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
      split_ifs <;> simp
    rw [hk,Basis.coord_apply,Basis.repr_self,Finsupp.single_apply]
  change (nativeRationalFirstLayerRealBasis D L).coord j w = _
  rw [← hcoord]
  exact hf w

end Hindman168
