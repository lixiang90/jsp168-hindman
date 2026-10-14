import Hindman168.NativeOriginalRealBoxObstruction
import Hindman168.RoughResidueBoxNormalization
import Hindman168.RoughSpatialAffineSubstitution

/-! ACTUAL original residue-box Haar discrepancy now PRODUCES one true
original horizontal character and ALL original affine coefficient rows.
Finite list and constants precede every step, residue, source, parameter, box
and observable. No scalar/cube/box inverse or production premise remains. -/
namespace Hindman168
open MeasureTheory MvPolynomial
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_original_residue_box_obstruction {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ S : Finset (D.E →ₗ[ℝ] ℝ),
      (∀ χ ∈ S, RoughNativeHorizontalFunctional (I := D.I) D.Γ χ) ∧
      ∃ A Z0 : ℝ, 0 < A ∧ 1 ≤ Z0 ∧
      ∀ (t : ℕ), 0 < t → ∀ Z : ℝ, Z0 ≤ Z/t → (t : ℝ) ≤ Z → (t : ℝ) ≤ (c/2)*Z →
      ∀ lo hi v : Fin n → ℤ,
        (∀ j, c*Z ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*Z) →
        (∀ j, |(lo j : ℝ)| ≤ C*Z ∧ |(hi j : ℝ)| ≤ C*Z) →
      ∀ (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
        RoughVectorMvDegreeLE p d →
        (∀ x, nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) = roughVectorMvEval p x) →
      ∀ z : ℝ, ∀ F : C(D.G ⧸ D.Γ, ℂ), LipschitzWith L F → (∀ q, ‖F q‖ ≤ B) →
        η ≤ ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
          (fun x => F (Q (fun i => i.elim z (fun j => (x j : ℝ))) : D.G ⧸ D.Γ)) -
            ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ →
        ∃ χ ∈ S, ∃ b : Fin n → ℕ, (∀ j, b j < t ∧ (b j : ℤ)=v j%(t : ℤ)) ∧
          ∀ J : Fin n → ℕ, 0 < (∑ j, J j) →
            ‖((coeff (Finsupp.equivFunOnFinite.symm J)
              (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => (t : ℝ))
                (roughScalarSpatialProjection χ p z)) : ℝ) : UnitAddCircle)‖ ≤
                  A*((t : ℝ)/Z)^(∑ j, J j) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,A,Z0,hA,hZ0,hBox⟩ := native_original_real_box_finite_obstruction D n d
    (c/2) (C+1) B η L (by positivity) (by positivity) hB hη
  refine ⟨S,hS,A,Z0,hA,hZ0,?_⟩
  intro t ht Z hZ htZ htc lo hi v hLen hLoc Q p hp hQ z F hF hBound hBad
  have htI : (0 : ℤ) < t := by exact_mod_cast ht
  let b : Fin n → ℕ := fun j => (v j%(t : ℤ)).toNat
  have hbCast (j : Fin n) : (b j : ℤ)=v j%(t : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ htI.ne')
  have hb (j : Fin n) : b j < t := by
    have h : (b j : ℤ) < t := by rw [hbCast]; exact Int.emod_lt_of_pos _ htI
    exact_mod_cast h
  have hbReal (j : Fin n) : (b j : ℝ)=((v j%(t : ℤ) : ℤ) : ℝ) := by exact_mod_cast hbCast j
  let u : Option (Fin n) → ℝ := fun i => i.elim 0 (fun j => (b j : ℝ))
  let k : Option (Fin n) → ℝ := fun i => i.elim 1 (fun _ => (t : ℝ))
  let r := roughVectorMvAffineSubstitution u k p
  let R := fun x : Option (Fin n) → ℝ => Q (fun i => u i+k i*x i)
  have hr : RoughVectorMvDegreeLE r d := roughVectorMvAffineSubstitution_degree u k hp
  have hR (x : Option (Fin n) → ℝ) :
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (R x)=roughVectorMvEval r x := by
    rw [roughVectorMvAffineSubstitution_eval]
    exact hQ _
  let low := fun j => (alignmentRetainedEndpoint (lo j) t (v j%t) : ℝ)
  let high := fun j => (alignmentRetainedEndpoint (hi j) t (v j%t) : ℝ)
  obtain ⟨hMin,hLow,hHigh⟩ := rough_residue_box_normalized_geometry lo hi v t ht Z c C hLen hLoc htc htZ
  have hBad' : η ≤ ‖finiteComplexSetMean (roughRealIntegerBox low high)
      (fun x => F (R (fun i => i.elim z (fun j => (x j : ℝ))) : D.G ⧸ D.Γ)) -
        ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ := by
    rw [rough_residue_box_normalized_mean lo hi v t ht] at hBad
    have he (x : Fin n → ℤ) :
        Q (fun i => i.elim z (fun j => ((v j%(t : ℤ)+(t : ℤ)*x j : ℤ) : ℝ))) =
          R (fun i => i.elim z (fun j => (x j : ℝ))) := by
      congr 1
      funext i
      cases i <;> simp only [u,k,Option.elim_none,Option.elim_some,zero_add,one_mul,
        Int.cast_add,Int.cast_mul,Int.cast_natCast,hbReal]
    simpa only [low,high,he] using hBad
  obtain ⟨χ,hχ,hCoeff⟩ := hBox (Z/t) hZ low high hMin hLow hHigh R r hr hR z F hF hBound hBad'
  refine ⟨χ,hχ,b,fun j => ⟨hb j,hbCast j⟩,?_⟩
  intro J hJ
  simpa only [r,u,k,rough_spatial_affine_vector_projection,inv_div] using hCoeff J hJ

end Hindman168
