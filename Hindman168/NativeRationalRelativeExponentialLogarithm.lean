import Hindman168.NativeRationalRelativeInclusion

/-! Actual native inclusion and Exp/Log compatibility for arbitrary rational relative layers. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_data_exponential {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (v : (nativeRationalRelativeData D F i).E) :
    nativeRationalRelativeGroupInclusion D F i
      (nativeLieExponential (E := (nativeRationalRelativeData D F i).E)
        (I := (nativeRationalRelativeData D F i).I) (G := (nativeRationalRelativeData D F i).G) v) =
      nativeLieExponential (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRationalRelativeModelInclusion D F i v) := by
  have h := nativeLieExponential_map (I := (nativeRationalRelativeData D F i).I)
    (J := D.I.prod D.I) (nativeRationalRelativeGroupInclusion D F i)
    ((native_rational_relative_inclusion_contMDiff D F i).mdifferentiable (by norm_num)) v
  rw [native_rational_relative_inclusion_mfderiv] at h
  exact h

theorem native_rational_relative_data_logarithm {s ℓ : ℕ} (D : NativeNilmanifoldData.{u} s)
    (F : NativeRationalLieFiltration D ℓ) (i : ℕ) (g : (nativeRationalRelativeData D F i).G) :
    letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
    nativeRationalRelativeModelInclusion D F i
      (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D F i).E)
        (I := (nativeRationalRelativeData D F i).I) (G := (nativeRationalRelativeData D F i).G) g) =
      nativeLieGlobalLogarithm (E := D.E × D.E) (I := D.I.prod D.I) (G := D.G × D.G)
        (nativeRationalRelativeGroupInclusion D F i g) := by
  letI := nativeProductGroup_simplyConnected (I := D.I) (J := D.I) (G := D.G) (K := D.G)
  have h := native_rational_relative_data_exponential D F i
    (nativeLieGlobalLogarithm (E := (nativeRationalRelativeData D F i).E)
      (I := (nativeRationalRelativeData D F i).I) (G := (nativeRationalRelativeData D F i).G) g)
  rw [nativeLieExponential_globalLogarithm] at h
  have hl := congrArg (nativeLieGlobalLogarithm (E := D.E × D.E)
    (I := D.I.prod D.I) (G := D.G × D.G)) h
  rw [nativeLieGlobalLogarithm_exponential] at hl
  exact hl.symm

end Hindman168
