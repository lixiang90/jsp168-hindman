import Hindman168.NativeRelativeReducedLieFiltration
import Hindman168.NativeBasepointRelativeFilteredPolynomial
import Hindman168.NativeBasepointReducedPolynomial

/-! Genuine weights, real filteredness and ordinary degree decrease of
the actual reduced polynomial after removing zero vector terms. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_basepoint_reduced_polynomial_weighted {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughVectorMvWeightedDegree (nativeRelativeReducedLieFiltration D d hd)
      (nativeBasepointReducedPolynomial D d hd p hp r t h) 0 := by
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact Submodule.mem_map_of_mem
    (native_basepoint_relative_polynomial_weighted D d hd p hp r t h b hb)

theorem native_basepoint_reduced_real_polynomial_filtered {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughFilteredPolynomial (nativeRelativeReducedNativeFiltration D d hd)
      (fun x : Unit → ℝ => nativeLieExponential (E := (nativeRelativeReducedData D d hd).E)
        (I := (nativeRelativeReducedData D d hd).I) (G := (nativeRelativeReducedData D d hd).G)
        (roughVectorMvEval (E := (nativeRelativeReducedData D d hd).E)
          (nativeBasepointReducedPolynomial D d hd p hp r t h) x)) :=
  native_arbitrary_lie_polynomial_filtered (nativeRelativeReducedData D d hd)
    (nativeRelativeReducedLieFiltration D d hd) (native_relative_reduced_lie_filtration_antitone D d hd)
    (fun _ _ _ _ hv hw => native_relative_reduced_lie_filtration_bracket D d hd hv hw)
    (nativeRelativeReducedNativeFiltration D d hd)
    (fun i _ hv => native_relative_reduced_lie_filtration_exponential_mem D d hd i hv) _
    (native_basepoint_reduced_polynomial_weighted D d hd p hp r t h)

theorem native_basepoint_reduced_zero_trim_degree_drop {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) :
    RoughVectorMvDegreeLE (roughVectorMvZeroTrim (nativeBasepointReducedPolynomial D d hd p hp r t h)) (s*d-1) := by
  have he := rough_vector_zero_trim_degree (nativeRelativeReducedLieFiltration D d hd)
    (native_relative_reduced_lie_filtration_antitone D d hd)
    (native_basepoint_reduced_polynomial_weighted D d hd p hp r t h)
    (native_relative_reduced_lie_filtration_terminal D d hd (s*d-1+1) (by omega))
  simpa only [Nat.sub_zero] using he

theorem native_basepoint_reduced_coefficient_terminal {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvDegreeLE p d)
    (r t : D.G) (h : ℤ) (J : Unit →₀ ℕ) (hJ : s*d ≤ J.sum (fun _ n => n)) :
    roughVectorMvCoefficient (nativeBasepointReducedPolynomial D d hd p hp r t h) J = 0 := by
  have hm := rough_vector_weighted_coefficient (nativeRelativeReducedLieFiltration D d hd)
    (native_relative_reduced_lie_filtration_antitone D d hd)
    (native_basepoint_reduced_polynomial_weighted D d hd p hp r t h) J
  rw [Nat.add_zero,native_relative_reduced_lie_filtration_terminal D d hd _ hJ,Submodule.mem_bot] at hm
  exact hm

end Hindman168
