import Hindman168.NativeDiagonalCenterModel
import Hindman168.NativeCentralSubspaceSubgroup
import Hindman168.DiagonalCenterSubgroup

/-! The ACTUAL exponential subgroup of the ORIGINAL diagonal center model
is EXACTLY the ACTUAL original diagonal center, not a substitute subgroup. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_diagonal_center_exponential_subgroup {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeCentralSubspaceSubgroup (I := D.I.prod D.I) (G := D.G × D.G)
      (nativeDiagonalCenterModel D) (native_diagonal_center_model_le D) = diagonalCenterSubgroup D.G := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  ext g
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨w,rfl⟩ := (native_diagonal_center_model_mem D v).mp hv
    change nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (w.val,w.val) ∈ diagonalCenterSubgroup D.G
    rw [nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G)]
    apply (diagonal_center_mem_iff D.G _).mpr
    exact ⟨⟨nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w.val,
      (nativeLieExponential_mem_center_iff_mem_centerModel (I := D.I) (G := D.G) w.val).mpr w.property⟩,rfl⟩
  · intro hg
    obtain ⟨z,rfl⟩ := (diagonal_center_mem_iff D.G g).mp hg
    let w : nativeLieCenterModel (I := D.I) (G := D.G) :=
      ⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) z.val,
        (nativeLieGlobalLogarithm_mem_centerModel_iff (I := D.I) (G := D.G) z.val).mpr z.property⟩
    refine ⟨(w.val,w.val),(native_diagonal_center_model_mem D _).mpr ⟨w,rfl⟩,?_⟩
    change nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
      (w.val,w.val) = (z.val,z.val)
    rw [nativeProductExponential_eq (I := D.I) (J := D.I) (G := D.G) (K := D.G)]
    have h : nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w.val = z.val :=
      nativeLieExponential_globalLogarithm (I := D.I) (G := D.G) z.val
    exact Prod.ext h h

end Hindman168
