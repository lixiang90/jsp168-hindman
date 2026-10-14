import Hindman168.RoughNativeProductWeighted
import Hindman168.RoughVectorZeroTrim
import Hindman168.RoughNativePolynomialFiltered
import Hindman168.NativeNilmanifoldData
import Hindman168.NativeLieRationalPowerMembership
import Hindman168.RoughNativeStretchedLieTerminal

/-! The actual original right correction P(n)*gamma^(-n) is represented
by a true native logarithmic polynomial with the original Lie weights. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLinearStepCorrection {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (γ : D.G) : RoughVectorMvPolynomial Unit D.E :=
  [(MvPolynomial.X (),-nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ)]

noncomputable def nativeLinearStepRawPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G) :
    RoughVectorMvPolynomial Unit D.E :=
  roughNativeProductMvPolynomial (I := D.I) (G := D.G) p (nativeLinearStepCorrection D γ)

noncomputable def nativeLinearStepPolynomial {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G) :
    RoughVectorMvPolynomial Unit D.E := roughVectorMvZeroTrim (nativeLinearStepRawPolynomial D p γ)

theorem native_linear_step_correction_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (γ : D.G) (x : Unit → ℝ) :
    roughVectorMvEval (nativeLinearStepCorrection D γ) x =
      (-x ()) • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ := by
  simp only [nativeLinearStepCorrection,roughVectorMvEval,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,MvPolynomial.eval_X,smul_neg,neg_smul]

theorem native_linear_step_polynomial_eval {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G) (x : Unit → ℝ) :
    roughVectorMvEval (nativeLinearStepPolynomial D p γ) x =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x) *
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            ((-x ()) • nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) γ)) := by
  rw [nativeLinearStepPolynomial,rough_vector_zero_trim_eval,nativeLinearStepRawPolynomial,
    roughNativeProductMvPolynomial_eval,native_linear_step_correction_eval]

theorem native_linear_step_integer_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (γ : D.G) (n : ℤ) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (nativeLinearStepPolynomial D p γ) (fun _ => (n : ℝ))) =
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) p (fun _ => (n : ℝ))) * γ ^ (-n) := by
  rw [native_linear_step_polynomial_eval,nativeLieExponential_globalLogarithm,
    ← Int.cast_neg,nativeLieExponential_int_smul,nativeLieExponential_globalLogarithm]

theorem native_linear_step_raw_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial Unit D.E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (γ : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeLinearStepRawPolynomial D p γ) 0 := by
  apply rough_native_product_polynomial_weighted d hd hp
  intro a ha
  obtain rfl := List.mem_singleton.mp ha
  rw [MvPolynomial.totalDegree_X,Nat.add_zero,rough_native_stretched_lie_initial d hd 1 hd]
  exact Submodule.mem_top

theorem native_linear_step_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial Unit D.E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (γ : D.G) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d)
      (nativeLinearStepPolynomial D p γ) 0 :=
  rough_vector_zero_trim_weighted _ (native_linear_step_raw_weighted D d hd hp γ)

theorem native_linear_step_polynomial_degree {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    {p : RoughVectorMvPolynomial Unit D.E}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := D.I) (G := D.G) d) p 0)
    (γ : D.G) : RoughVectorMvDegreeLE (nativeLinearStepPolynomial D p γ) (s*d) :=
  rough_vector_zero_trim_degree _ (rough_native_stretched_lie_antitone d hd)
    (native_linear_step_raw_weighted D d hd hp γ) (rough_native_stretched_lie_terminal d hd D.step_le)

end Hindman168
