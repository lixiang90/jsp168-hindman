import Hindman168.NativeResidueCubeFiniteEscape
import Hindman168.NativeOriginalResidueBoxObstruction

/-! Actual cube Haar convergence on every translated fixed-progression box.
The threshold precedes all box endpoints, residue vectors and bounded Lipschitz tests. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_progression_box_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (t : ℕ) (ht : 0 < t)
    (c R B η : ℝ) (T : NNReal) (hc : 0 < c) (hR : 0 ≤ R) (hB : 0 ≤ B) (hη : 0 < η) :
    let A := nativeResidueCubeData D F ρ hρ d n e
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ m in atTop, ∀ lo hi v : Fin (d+1) → ℤ,
      (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
      (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
      ∀ z : ℝ, ∀ f : C(A.G ⧸ A.Γ, ℂ), LipschitzWith T f → (∀ q, ‖f q‖ ≤ B) →
        ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
          (fun x => f (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
            (fun i => i.elim z (fun j => (x j : ℝ))) : A.G ⧸ A.Γ)) -
              ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < η := by
  classical
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨S,hS,K,Z0,hK,_hZ0,hInv⟩ :=
    native_original_residue_box_obstruction A (d+1) ℓ c R B η T hc hR hB hη
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hEscape := native_residue_cube_finite_affine_escape D F ρ hρ d n e L p hp hIrr
    S hS (t : ℚ) htQ (K*(t : ℝ)^ℓ)
  filter_upwards [hEscape, hL.eventually_ge_atTop ((t : ℝ)*Z0),
    hL.eventually_ge_atTop (t : ℝ), hL.eventually_ge_atTop ((t : ℝ)/(c/2))] with m hm hLarge htL hfrac
  intro lo hi v hlen hloc z f hf hbound
  have hpos : 0 < L m := htR.trans_le htL
  have hZ : Z0 ≤ L m/(t : ℝ) := (le_div_iff₀ htR).mpr (by simpa only [mul_comm] using hLarge)
  have htc : (t : ℝ) ≤ (c/2)*L m := by
    have hh := (div_le_iff₀ (half_pos hc)).mp hfrac
    simpa only [mul_comm] using hh
  by_contra hbad
  obtain ⟨chi,hchi,b,_hb,hcoeff⟩ := hInv t ht (L m) hZ htL htc lo hi v hlen hloc
    (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m))
    (nativeResidueCubeSpatialPolynomial D F ρ hρ d n e (p m) (hp m))
    (native_residue_cube_spatial_degree D F ρ hρ d n e (p m) (hp m))
    (native_residue_cube_spatial_log D F ρ hρ d n e (p m) (hp m))
    z f hf hbound (le_of_not_gt hbad)
  obtain ⟨J,hJ,hJTop,hBig⟩ := hm chi hchi
  have hs := mul_le_mul_of_nonneg_left (hcoeff J hJ) (pow_nonneg hpos.le (∑ i, J i))
  have hcancel : (L m)^(∑ i, J i) * (K*((t : ℝ)/L m)^(∑ i, J i)) = K*(t : ℝ)^(∑ i, J i) := by
    calc
      _ = K*(L m*((t : ℝ)/L m))^(∑ i, J i) := by rw [mul_pow]; ring
      _ = _ := by congr 2; field_simp
  have hsmall := hs.trans_eq hcancel
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hbound' := hsmall.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 hJTop) hK.le)
  have hbig := hBig z (fun i => (b i : ℝ))
  simp only [Rat.cast_natCast] at hbig
  exact (not_lt_of_ge hbound') hbig

end Hindman168
