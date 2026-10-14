import Hindman168.NativeResidueCubeFiniteEscape
import Hindman168.NativeOriginalRealBoxObstruction

/-! Actual residue-cube Haar convergence on real integer boxes, uniformly in
box endpoints and bounded Lipschitz tests. ALL original cube variables vary. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_real_box_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (c R B η : ℝ) (T : NNReal) (hc : 0 < c) (hR : 0 ≤ R) (hB : 0 ≤ B) (hη : 0 < η) :
    let A := nativeResidueCubeData D F ρ hρ d n e
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ m in atTop, ∀ lo hi : Fin (d+1) → ℝ,
      (∀ i, c*L m ≤ hi i-lo i) → (∀ i, -R*L m ≤ lo i) → (∀ i, hi i ≤ R*L m) →
      ∀ z : ℝ, ∀ f : C(A.G ⧸ A.Γ, ℂ), LipschitzWith T f → (∀ q, ‖f q‖ ≤ B) →
        ‖finiteComplexSetMean (roughRealIntegerBox lo hi)
          (fun x => f (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
            (fun i => i.elim z (fun j => (x j : ℝ))) : A.G ⧸ A.Γ)) -
              ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < η := by
  classical
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,K,Z0,_hK,hZ0,hInv⟩ :=
    native_original_real_box_finite_obstruction A (d+1) ℓ c R B η T hc hR hB hη
  have hEscape := native_residue_cube_finite_affine_escape D F ρ hρ d n e L p hp hIrr
    S hS 1 (by norm_num) K
  filter_upwards [hEscape, hL.eventually_ge_atTop Z0] with m hm hLarge
  intro lo hi hlen hlo hhi z f hf hbound
  have hpos : 0 < L m := zero_lt_one.trans_le (hZ0.trans hLarge)
  by_contra hbad
  obtain ⟨chi,hchi,hcoeff⟩ := hInv (L m) hLarge lo hi hlen hlo hhi
    (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m))
    (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e (p m) (hp m))
    (native_residue_cube_spatial_degree D F ρ hρ d n e (p m) (hp m))
    (native_residue_cube_spatial_log D F ρ hρ d n e (p m) (hp m))
    z f hf hbound (le_of_not_gt hbad)
  obtain ⟨J,hJ,_hJTop,hBig⟩ := hm chi hchi
  have hs := mul_le_mul_of_nonneg_left (hcoeff J hJ) (pow_nonneg hpos.le (∑ i, J i))
  have hcancel : (L m)^(∑ i, J i) * (K*(L m)⁻¹^(∑ i, J i)) = K := by
    calc
      _ = K*((L m)^(∑ i, J i)*(L m)⁻¹^(∑ i, J i)) := by ring
      _ = K := by rw [← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, mul_one]
  have hsmall := hs.trans_eq hcancel
  have hbig := hBig z (fun _ => 0)
  have hid (P : MvPolynomial (Fin (d+1)) ℝ) :
      roughMvAffineSubstitution (fun _ => 0) (fun _ => ((1 : ℚ) : ℝ)) P = P := by
    apply MvPolynomial.funext
    intro x
    rw [roughMvAffineSubstitution_eval]
    simp
  rw [hid] at hbig
  exact (not_lt_of_ge hsmall) hbig

end Hindman168
