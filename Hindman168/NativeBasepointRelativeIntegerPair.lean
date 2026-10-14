import Hindman168.NativeBasepointTrimmedPolynomial
import Hindman168.NativeNormalizedIntegerPair

/-! GENERAL starting-value normalization feeds the SAME original native
relative group, with original stretch d retained through actual weights.
No enlarged ordinary-degree filtration or relative-degree premise is used. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_integer_sequence_eq {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r : D.G) (n : ℤ) :
    nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) n =
      roughGroupBasepointNormalization (nativeIntegerLogPolynomialSequence D p) r n := by
  rw [nativeIntegerLogPolynomialSequence,native_basepoint_polynomial_exp]
  simp only [roughGroupBasepointNormalization,nativeIntegerLogPolynomialSequence,Int.cast_zero]
  have he : (0 : Unit → ℝ) = (fun _ : Unit => (0 : ℝ)) := by
    funext i
    rfl
  rw [he]

theorem native_basepoint_integer_sequence_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (r : D.G) :
    nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r) 0 = 1 := by
  rw [native_basepoint_integer_sequence_eq,rough_group_basepoint_normalization_zero]

theorem native_basepoint_integer_sequence_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) (r : D.G) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) := by
  let c : ℤ →+ (Unit → ℤ) := {
    toFun := fun n _ => n
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact rough_filtered_polynomial_precompose _ _
    (native_basepoint_integer_polynomial_filtered D d hd p hp r) c

theorem native_basepoint_relative_integer_pair_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n ∈
      nativeRelativeSquareFiltration D d 1 := by
  letI := rough_stretched_filtration_normal (G := D.G) d 2
  exact rough_normalized_integer_pair_mem _ (rough_stretched_filtration_conditions d hd)
    (rough_stretched_filtration_one d hd) _
    (native_basepoint_integer_sequence_filtered D d hd p hp r)
    (native_basepoint_integer_sequence_zero D p r) t h n

noncomputable def nativeBasepointRelativeIntegerPair {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) : (nativeRelativeSquareData D d hd 1).G :=
  ⟨roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n,
    native_basepoint_relative_integer_pair_mem D d hd p hp r t h n⟩

theorem native_basepoint_relative_integer_pair_inclusion {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h n : ℤ) :
    nativeRelativeGroupInclusion D d hd 1 (nativeBasepointRelativeIntegerPair D d hd p hp r t h n) =
      roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D (nativeBasepointPolynomial D p r)) t h n := rfl

end Hindman168
