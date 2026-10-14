import Hindman168.NativeRelativeRationalInclusion
import Hindman168.NativeRelativeLieFiltration
import Hindman168.RationalRealSpanTransport

/-! Every true internal relative Lie layer is rational for the true
restricted product lattice, including the initial layer zero. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_ambient_lie_layer_antitone {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) :
    Antitone (nativeRelativeSquareModel D d) := by
  intro i j hij
  have he := relative_linear_filtration_antitone _
    (rough_native_stretched_lie_antitone (I := D.I) (G := D.G) d hd) hij
  rw [native_relative_ambient_lie_layer_eq D d j,native_relative_ambient_lie_layer_eq D d i] at he
  exact he

theorem native_relative_lie_layer_rational {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ) :
    nativeLatticeRationalSubspace (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ
        (nativeRelativeLieFiltration D d hd i) := by
  cases i with
  | zero =>
    rw [native_relative_lie_filtration_zero D d hd]
    unfold nativeLatticeRationalSubspace
    simp only [Submodule.restrictScalars_top,top_inf_eq]
    exact nativeSubgroupRationalLogSpan_real_span_eq_top
      (E := (nativeRelativeSquareData D d hd 1).E)
      (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ
  | succ i =>
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    let L := (nativeRelativeModelInclusion D d hd 1).toLinearMap
    have hL : Function.Injective L := Subtype.val_injective
    have hRange : nativeRelativeSquareModel D d (i+1) ≤ LinearMap.range L := by
      intro v hv
      have hv1 := (native_relative_ambient_lie_layer_antitone D d hd) (Nat.le_add_left 1 i) hv
      rw [← native_relative_square_native_model_eq D d 1] at hv1
      exact ⟨⟨v,hv1⟩,rfl⟩
    exact rational_real_span_comap L hL (nativeRelativeSquareModel D d (i+1)) hRange
      (nativeSubgroupRationalLogSpan (E := (nativeRelativeSquareData D d hd 1).E)
        (I := (nativeRelativeSquareData D d hd 1).I) (nativeRelativeSquareData D d hd 1).Γ)
      (nativeSubgroupRationalLogSpan (E := D.E × D.E) (I := D.I.prod D.I) (D.Γ.prod D.Γ))
      (native_relative_rational_inclusion_iff D d hd)
      (native_relative_square_model_rational D d hd (i+1))

end Hindman168
