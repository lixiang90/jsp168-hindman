import Hindman168.RoughNormalizedIntegerPair
import Hindman168.NativeRelativeInclusion
import Hindman168.RoughNativePolynomialFiltered

/-! Actual original ordinary logarithmic polynomials give the genuine
normalized shifted pair in the SAME native relative group. Starting log
value zero is explicit here; general starting-value normalization and full
relative filtered polynomial degree remain separate tasks. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeIntegerLogPolynomialSequence {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (n : ℤ) : D.G :=
  nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ)))

theorem native_integer_log_polynomial_sequence_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d) :
    RoughFilteredPolynomial (roughStretchedLowerCentralFiltration D.G d)
      (nativeIntegerLogPolynomialSequence D p) := by
  let c : ℤ →+ (Unit → ℤ) := {
    toFun := fun n _ => n
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact rough_filtered_polynomial_precompose _ _
    (rough_native_integer_log_polynomial_filtered (I := D.I) (G := D.G) d hd hp) c

theorem native_integer_log_polynomial_sequence_zero {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0) :
    nativeIntegerLogPolynomialSequence D p 0 = 1 := by
  simp only [nativeIntegerLogPolynomialSequence,Int.cast_zero,h0]
  exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)

theorem native_normalized_integer_polynomial_pair_mem {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0) (r : D.G) (h n : ℤ) :
    roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n ∈
      nativeRelativeSquareFiltration D d 1 := by
  letI := rough_stretched_filtration_normal (G := D.G) d 2
  exact rough_normalized_integer_pair_mem _ (rough_stretched_filtration_conditions d hd)
    (rough_stretched_filtration_one d hd) _
    (native_integer_log_polynomial_sequence_filtered D d hd p hp)
    (native_integer_log_polynomial_sequence_zero D p h0) r h n

noncomputable def nativeNormalizedIntegerPolynomialPair {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0) (r : D.G) (h n : ℤ) :
    (nativeRelativeSquareData D d hd 1).G :=
  ⟨roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n,
    native_normalized_integer_polynomial_pair_mem D d hd p hp h0 r h n⟩

theorem native_normalized_integer_polynomial_pair_inclusion {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (h0 : roughVectorMvEval p (fun _ => 0) = 0) (r : D.G) (h n : ℤ) :
    nativeRelativeGroupInclusion D d hd 1
      (nativeNormalizedIntegerPolynomialPair D d hd p hp h0 r h n) =
      roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) r h n := rfl

end Hindman168
