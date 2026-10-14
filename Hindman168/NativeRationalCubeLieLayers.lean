import Hindman168.NativeRationalSubgroupFiltration
import Hindman168.UpperFaceLieCoordinates
import Hindman168.UpperFaceLieRestrictedSpan

/-! Cube Lie layers of the SAME final native rational subgroup filtration.
The initial layer may be a proper subspace of the original native algebra. -/
namespace Hindman168
open scoped Manifold ContDiff
attribute [local instance] lieGroup_smooth_min_three pointwiseLieRing pointwiseLieAlgebra
universe u

theorem native_rational_subgroup_lie_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i j : ℕ) (x y : GroupLieAlgebra D.I D.G) (hx : x ∈ F.layer i) (hy : y ∈ F.layer j) :
    ⁅x,y⁆ ∈ F.layer (i+j) := by
  have hm := F.bracket i j x y hx hy
  rw [← nativeLieAdjointGenerator_eq_differential] at hm
  exact (nativeLieAdjointGenerator_eq_native_bracket (I := D.I) (G := D.G) x y) ▸ hm

noncomputable def nativeRationalCubeLieAlgebra {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (d : ℕ) :
    LieSubalgebra ℝ (Finset (Fin d) → GroupLieAlgebra D.I D.G) :=
  upperFaceLieAlgebra (L := GroupLieAlgebra D.I D.G) F.layer F.antitone (native_rational_subgroup_lie_bracket D F) d

theorem native_rational_cube_lie_layer_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d i j : ℕ) {x y : Finset (Fin d) → GroupLieAlgebra D.I D.G}
    (hx : x ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d i) (hy : y ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d j) :
    ⁅x,y⁆ ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d (i+j) :=
  upper_face_lie_layer_bracket (L := GroupLieAlgebra D.I D.G) F.layer F.antitone (native_rational_subgroup_lie_bracket D F) d i j hx hy

theorem native_rational_cube_lie_layer_rational_span {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (d i : ℕ) :
    Submodule.span ℝ {z : Finset (Fin d) → GroupLieAlgebra D.I D.G |
      z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d i ∧
      ∀ V, z V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ} =
      upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d i := by
  apply upper_face_lie_layer_restricted_span (L := GroupLieAlgebra D.I D.G) F.layer _ (Submodule.zero_mem _) _ d i
  intro k
  exact F.rational k

end Hindman168
