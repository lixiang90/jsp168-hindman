import Hindman168.NativeBasepointRelativeFilteredPolynomial
import Hindman168.NativeBasepointReducedPolynomial
import Hindman168.NativeRelativeReducedNativeFiltration
import Hindman168.RoughFilteredIntegerLinearPart

/-! ACTUAL reduced original normalized polynomial is genuinely filtered
on SAME native terminal quotient; its actual filtration terminates at s*d,
one derivative earlier than the original degree-s*d filtration. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeBasepointReducedIntegerSequence {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) : (nativeRelativeReducedData D d hd).G :=
  nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
    (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)
    (roughVectorMvEval (E := (nativeRelativeReducedData D d hd).E)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) (fun _ => (n : ℝ)))

theorem native_basepoint_reduced_integer_sequence_projection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    nativeBasepointReducedIntegerSequence D d hd p hp r t h n =
      nativeRelativeReductionGroupProjection D d hd (nativeBasepointRelativeIntegerPair D d hd p hp r t h n) := by
  unfold nativeBasepointReducedIntegerSequence
  rw [native_basepoint_reduced_polynomial_eval]
  exact (native_relative_reduction_data_exponential D d hd
    (roughVectorMvEval (E := (nativeRelativeSquareData D d hd 1).E)
      (nativeBasepointRelativePolynomial D d hd p hp r t h) (fun _ => (n : ℝ)))).symm.trans
        (congrArg (nativeRelativeReductionGroupProjection D d hd)
          (native_basepoint_relative_polynomial_exponential D d hd p hp r t h n))

theorem native_relative_internal_layer_projection_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (i : ℕ)
    {g : (nativeRelativeSquareData D d hd 1).G} (hg : g ∈ nativeRelativeSquareInternalFiltration D d i) :
    nativeRelativeReductionGroupProjection D d hd g ∈ nativeRelativeReducedNativeFiltration D d hd i := by
  letI := native_relative_terminal_subgroup_normal D d hd
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (nativeRelativeTerminalSubgroup D d hd)) hg

theorem native_basepoint_reduced_integer_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRelativeReducedNativeFiltration D d hd)
      (nativeBasepointReducedIntegerSequence D d hd p hp r t h) := by
  intro hs n
  have hP := native_basepoint_relative_integer_polynomial_filtered D d hd p hp r t h
  have he : nativeBasepointReducedIntegerSequence D d hd p hp r t h =
      fun m => nativeRelativeReductionGroupProjection D d hd (nativeBasepointRelativeIntegerPair D d hd p hp r t h m) :=
    funext (native_basepoint_reduced_integer_sequence_projection D d hd p hp r t h)
  rw [he,rough_iterated_group_difference_hom]
  exact native_relative_internal_layer_projection_mem D d hd hs.length (hP hs n)

theorem native_basepoint_reduced_integer_polynomial_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (hs : List ℤ) (hLen : s*d ≤ hs.length) (n : ℤ) :
    roughIteratedGroupDifference (nativeBasepointReducedIntegerSequence D d hd p hp r t h) hs n = 1 := by
  have hm := native_basepoint_reduced_integer_polynomial_filtered D d hd p hp r t h hs n
  rw [native_relative_reduced_native_filtration_beyond_terminal D d hd hs.length hLen,Subgroup.mem_bot] at hm
  exact hm

theorem native_basepoint_reduced_integer_polynomial_degree_drop {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (hs : List ℤ) (hLen : s*d-1 < hs.length) (n : ℤ) :
    roughIteratedGroupDifference (nativeBasepointReducedIntegerSequence D d hd p hp r t h) hs n = 1 :=
  native_basepoint_reduced_integer_polynomial_terminal D d hd p hp r t h hs (by omega) n

end Hindman168
