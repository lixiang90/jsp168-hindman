import Hindman168.NativeRelativeInclusion

/-! Genuine ACTUAL relative native Exp/Log are exactly compatible
with ORIGINAL product group/model inclusions, by true smooth-hom uniqueness. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_relative_data_exponential {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) (v : (nativeRelativeSquareData D d hd i).E) :
    nativeRelativeGroupInclusion D d hd i
      (nativeLieExponential (E := (nativeRelativeSquareData D d hd i).E)
        (I := (nativeRelativeSquareData D d hd i).I) (G := (nativeRelativeSquareData D d hd i).G) v) =
      nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRelativeModelInclusion D d hd i v) := by
  have h := nativeLieExponential_map (I := (nativeRelativeSquareData D d hd i).I)
    (J := D.I.prod D.I) (nativeRelativeGroupInclusion D d hd i)
    ((native_relative_inclusion_contMDiff D d hd i).mdifferentiable (by norm_num)) v
  rw [native_relative_inclusion_mfderiv] at h
  exact h

theorem native_relative_data_logarithm {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d : ℕ) (hd : 0 < d) (i : ℕ) (g : (nativeRelativeSquareData D d hd i).G) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeRelativeModelInclusion D d hd i
      (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd i).E)
        (I := (nativeRelativeSquareData D d hd i).I) (G := (nativeRelativeSquareData D d hd i).G) g) =
      nativeLieGlobalLogarithm (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRelativeGroupInclusion D d hd i g) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have h := native_relative_data_exponential D d hd i
    (nativeLieGlobalLogarithm (E := (nativeRelativeSquareData D d hd i).E)
      (I := (nativeRelativeSquareData D d hd i).I) (G := (nativeRelativeSquareData D d hd i).G) g)
  rw [nativeLieExponential_globalLogarithm] at h
  have hl := congrArg (nativeLieGlobalLogarithm (E := D.E × D.E)
    (I := D.I.prod D.I) (G := D.G × D.G)) h
  rw [nativeLieGlobalLogarithm_exponential] at hl
  exact hl.symm

end Hindman168
