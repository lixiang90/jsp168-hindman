import Hindman168.CurvePicardImplicit

/-! The constructed implicit Picard curve really solves the ODE for
all nearby initial points. Its parameter derivative at the equilibrium
is computed at every time from the actual integral formula. -/

namespace Hindman168
open Set Metric Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 theorem curvePicard_fixed_hasDerivAt {f : E → E} {x : E} {α : C(Icc a b, E)}
    (hc : Continuous (fun s => f (α s))) (hfix : α = curvePicard hab t₀ f (x, α))
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (curveClippedExtension hab α) (f (curveClippedExtension hab α t)) t := by
  have hg : Continuous (fun s : ℝ => f (curveClippedExtension hab α s)) :=
    hc.comp continuous_projIcc
  have hd := (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable t₀ t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add x
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
  rw [curveClippedExtension, projIcc_of_mem hab hs']
  exact (congrArg (fun c : C(Icc a b, E) => c ⟨s, hs'⟩) hfix).trans
    (curvePicard_apply_of_continuous hab t₀ f x α hc ⟨s, hs'⟩)

 theorem curvePicardImplicit_eventually_continuous_field {f : E → E} {L : E →L[ℝ] E}
    {x : E} (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) :
    ∀ᶠ y in 𝓝 x, Continuous (fun t => f (curvePicardImplicit hab t₀ hf hL y t)) := by
  obtain ⟨C, U, hU, hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hU
  have hψ := (curvePicardImplicit_hasStrictFDerivAt hab t₀ hf hL).continuousAt
  have hn : curvePicardImplicit hab t₀ hf hL ⁻¹'
      ball (ContinuousMap.const (Icc a b) x) r ∈ 𝓝 x := by
    have hs := hψ.preimage_mem_nhds (ball_mem_nhds (curvePicardImplicit hab t₀ hf hL x) hr)
    rwa [curvePicardImplicit_self hab t₀ hf hL] at hs
  filter_upwards [hn] with y hy
  exact continuousOn_univ.mp (hLip.continuousOn.comp
    (curvePicardImplicit hab t₀ hf hL y).continuous.continuousOn (fun t _ => by
      apply hrs
      change dist (curvePicardImplicit hab t₀ hf hL y) (ContinuousMap.const (Icc a b) x) < r at hy
      rw [dist_eq_norm] at hy
      rw [mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt
        ((curvePicardImplicit hab t₀ hf hL y - ContinuousMap.const (Icc a b) x).norm_coe_le_norm t) hy))

 theorem curvePicardImplicit_eventually_integral {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (hx : f x = 0) :
    ∀ᶠ y in 𝓝 x,
      curvePicardImplicit hab t₀ hf hL y t₀ = y ∧
      ∀ t ∈ Ioo a b, HasDerivAt
        (curveClippedExtension hab (curvePicardImplicit hab t₀ hf hL y))
        (f (curveClippedExtension hab (curvePicardImplicit hab t₀ hf hL y) t)) t := by
  filter_upwards [curvePicardImplicit_eventually_fixed hab t₀ hf hL hx,
    curvePicardImplicit_eventually_continuous_field hab t₀ hf hL] with y hfix hc
  refine ⟨?_, fun t ht => curvePicard_fixed_hasDerivAt hab t₀ hc hfix ht⟩
  have h := (congrArg (fun c : C(Icc a b, E) => c t₀) hfix).trans
    (curvePicard_apply_of_continuous hab t₀ f y _ hc t₀)
  simpa only [intervalIntegral.integral_same, add_zero] using h

 theorem curvePicardImplicit_endpoint_hasStrictFDerivAt {f : E → E} {L : E →L[ℝ] E}
    {x : E} (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (t : Icc a b) :
    HasStrictFDerivAt (fun y => curvePicardImplicit hab t₀ hf hL y t)
      (ContinuousLinearMap.id ℝ E + ((t : ℝ) - t₀) • L) x := by
  have hd := (ContinuousMap.evalCLM ℝ t : C(Icc a b, E) →L[ℝ] E).hasStrictFDerivAt.comp x
    (curvePicardImplicit_hasStrictFDerivAt hab t₀ hf hL)
  apply hd.congr_fderiv
  ext y
  simp [curveVolterraLinearization, curveVolterra_apply, curveClippedExtension,
    intervalIntegral.integral_const]

 theorem exists_strict_equilibrium_local_flow {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (hx : f x = 0) :
    ∃ Φ : E → C(Icc a b, E), Φ x = ContinuousMap.const (Icc a b) x ∧
      (∀ t : Icc a b, HasStrictFDerivAt (fun y => Φ y t)
        (ContinuousLinearMap.id ℝ E + ((t : ℝ) - t₀) • L) x) ∧
      ∀ᶠ y in 𝓝 x, Φ y t₀ = y ∧ ∀ t ∈ Ioo a b,
        HasDerivAt (curveClippedExtension hab (Φ y))
          (f (curveClippedExtension hab (Φ y) t)) t := by
  exact ⟨curvePicardImplicit hab t₀ hf hL, curvePicardImplicit_self hab t₀ hf hL,
    fun t => curvePicardImplicit_endpoint_hasStrictFDerivAt hab t₀ hf hL t,
    curvePicardImplicit_eventually_integral hab t₀ hf hL hx⟩

end Hindman168
