import Hindman168.NativeRationalNonlinearScalarGeometry
import Hindman168.MvScalarTranslation

/-! COMPLETE actual scalar polynomial identity, recovered from all genuine
integer samples, not only a comparison of sampled values. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_relative_scalar_difference_polynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (t : D.G) (h : ℤ) :
    roughVectorMvProjection χ.toLinearMap (nativeRationalWeightedRelativePolynomial D L p hp h0 t h) =
      roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p +
      mvScalarTranslation (nativeRationalNonlinearScalar D L p hp h0 χ) (fun _ => (h : ℝ)) -
      nativeRationalNonlinearScalar D L p hp h0 χ +
      MvPolynomial.C (nativeRationalRelativeCommutatorValue D L χ
        (nativeIntegerLogPolynomialSequence D p 1) t)*MvPolynomial.X () := by
  apply MvPolynomial.funext_set (fun _ : Unit => Set.range (fun n : ℕ => (n : ℝ)))
    (fun _ => Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℝ))))
  intro x hx
  obtain ⟨n,hn⟩ := hx () (Set.mem_univ ())
  have he : x = (fun _ => (n : ℝ)) := by
    funext j
    cases j
    exact hn.symm
  rw [he,map_add,map_sub,map_add,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
    mv_scalar_translation_eval]
  have hf := native_rational_relative_scalar_difference_formula D L p hp h0 χ hχ t h (n : ℤ)
  simpa only [Int.cast_natCast,Int.cast_add,mul_comm] using hf

end Hindman168
