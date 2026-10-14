import Hindman168.NativeRationalLayerPointHaar
import Hindman168.NativeSubgroupAffineTopCoefficient

/-! Uniform q=0 Haar law on every translated fixed-rational-step window
whose length is at least a fixed positive fraction of the original scale.
The common threshold precedes every origin, window length and unit test.
In particular this covers signed integer origins and fixed nonzero integer
progression steps without altering the original irrational source. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_window_haar_unit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F (fun n => (N n : ℝ)) p)
    (d : ℚ) (hd : d ≠ 0) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    let A := nativeRationalLayerOrbitData D F 0 rho hRat
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ n in atTop, ∀ b : ℝ, ∀ m : ℕ, τ*(N n : ℝ) ≤ m →
      ∀ f ∈ unitLipschitzObservables (A.G ⧸ A.Γ),
      ‖finiteComplexSetMean (scalarMvIntegerCube Unit m)
        (fun x => f (QuotientGroup.mk (s := A.Γ) (show A.G from
          nativeRationalSubgroupPolynomialOrbit D F (p n) (hp n)
            (fun i => b + (d : ℝ)*(x i : ℝ))))) -
            ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ < δ := by
  classical
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨M,_hM,hInv⟩ := native_rational_layer_polynomial_inverse (σ := Unit) D F rho hRat δ hδ
  let T := roughNativeHorizontalCharacterGrid (I := A.I) A.Γ (M : ℝ)
  let ext := nativeSubgroupHorizontalExtension D F rho hRat
  let B : ℝ := (M : ℝ)*(τ⁻¹)^ℓ
  have hEscape : ∀ᶠ n in atTop, ∀ chi ∈ T, ∀ j ∈ Finset.Icc 1 ℓ,
      NativeSubgroupRationalLevelCharacter D F j (ext chi) →
      B < (N n : ℝ)^j * ‖(((d : ℝ)^j *
        (ext chi (roughVectorMvEval (adaptedTaylorResidual D (p n) j) (fun _ => (j : ℝ))) /
          (j.factorial : ℝ)) : ℝ) : UnitAddCircle)‖ := by
    apply (Filter.eventually_all_finset T).mpr
    intro chi _hchi
    apply (Filter.eventually_all_finset (Finset.Icc 1 ℓ)).mpr
    intro j hj
    by_cases hLevel : NativeSubgroupRationalLevelCharacter D F j (ext chi)
    · let q : ℚ := d^j / (j.factorial : ℚ)
      have hq : q ≠ 0 := div_ne_zero (pow_ne_zero _ hd) (by positivity)
      have h := hIrr j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 ((q : ℝ) • ext chi)
        (native_subgroup_level_character_rat_smul D F j (ext chi) hLevel q hq)
      have he (v : D.E) : ((q : ℝ) • ext chi) v = (d : ℝ)^j * (ext chi v / (j.factorial : ℝ)) := by
        change (q : ℝ) * ext chi v = _
        simp only [q, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
        ring
      simp only [he] at h
      exact (h.eventually_gt_atTop B).mono (fun _ hn _ => hn)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hLevel h))
  filter_upwards [hEscape, hN.eventually_gt_atTop 0] with n hn hpos
  intro b m hlen f hf
  have hm : 0 < m := by
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hpos
    have hmr : (0 : ℝ) < m := (mul_pos hτ hNr).trans_le hlen
    exact_mod_cast hmr
  let r := roughVectorMvAffineSubstitution (fun _ : Unit => b) (fun _ => (d : ℝ)) (p n)
  have hr : RoughVectorMvWeightedDegree F.layer r 0 :=
    rough_vector_weighted_affine F.layer F.antitone _ _ (hp n)
  have hOrbit (x : Unit → ℝ) : nativeRationalSubgroupPolynomialOrbit D F r hr x =
      nativeRationalSubgroupPolynomialOrbit D F (p n) (hp n) (fun i => b+(d : ℝ)*x i) := by
    apply Subtype.ext
    change nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) r x) = _
    rw [roughVectorMvAffineSubstitution_eval (E := D.E)]
    rfl
  by_contra hbad
  have hbad' : δ ≤ ‖finiteComplexSetMean (scalarMvIntegerCube Unit m)
      (fun x => f (QuotientGroup.mk (s := A.Γ) (show A.G from
        nativeRationalSubgroupPolynomialOrbit D F r hr (fun i => (x i : ℝ))))) -
          ∫ q, f q ∂nativeNilmanifoldQuotientProbability A‖ := by
    simpa only [hOrbit] using (le_of_not_gt hbad)
  obtain ⟨chi,hchi,j,hj,hjTop,hLevel,_hTail,hMono,_hBin⟩ := hInv r hr m hm f hf hbad'
  have hHor := ((rough_native_horizontal_grid_mem_iff A.Γ (M : ℝ) chi).mp hchi).2
  have hBracket := native_actual_subgroup_horizontal_extension_bracket D F rho hRat chi hHor
  have hsmall := hMono (fun _ : Unit => j) (by simpa using (show 0 < j by omega))
  have hindex : Finsupp.equivFunOnFinite.symm (fun _ : Unit => j) = Finsupp.single () j := by
    apply Finsupp.ext
    intro x
    cases x
    simp
  simp only [Finset.univ_unique, Finset.sum_singleton, hindex] at hsmall
  rw [native_subgroup_affine_top_coefficient D F (ext chi) hBracket j hLevel.2.1
    (p n) (hp n) b (d : ℝ)] at hsmall
  have hbound := finite_coefficient_scale_transfer (N n) m τ (M : ℝ) _ ℓ j hτ hτ1
    (Nat.cast_nonneg M) (norm_nonneg _) hlen hjTop hsmall
  exact (not_lt_of_ge hbound) (hn chi hchi j (Finset.mem_Icc.mpr ⟨hj,hjTop⟩) hLevel)

end Hindman168
