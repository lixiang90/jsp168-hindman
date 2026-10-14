import Hindman168.UnitCircleUniformFourierApproximation
import Mathlib.Analysis.Fourier.AddCircleMulti

namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical Topology

theorem unit_torus_fourier_uniform_approximation (κ : Type*) [Fintype κ]
    (F : C(UnitAddTorus κ, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : (κ → ℤ) →₀ ℂ, ‖F-c.sum (fun k a => a •
      (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ)))‖ < ε := by
  have hf : F ∈ (Submodule.span ℂ (Set.range
      (UnitAddTorus.mFourier : (κ → ℤ) → C(UnitAddTorus κ, ℂ)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]
    trivial
  change F ∈ closure ((Submodule.span ℂ (Set.range
    (UnitAddTorus.mFourier : (κ → ℤ) → C(UnitAddTorus κ, ℂ)))) : Set C(UnitAddTorus κ, ℂ)) at hf
  obtain ⟨G, hG, hclose⟩ := Metric.mem_closure_iff.mp hf ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  exact ⟨c, by simpa only [dist_eq_norm] using hclose⟩

/-- One actual finite Fourier family precedes all orbit coefficients,
sample lengths and arbitrary unit Lipschitz torus observables. -/
theorem unit_torus_finite_uniform_fourier_family (κ : Type*) [Fintype κ]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset ((κ → ℤ) →₀ ℂ), ∀ F ∈ unitLipschitzObservables (UnitAddTorus κ),
      ∃ c ∈ A, ‖F-c.sum (fun k a => a •
        (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ)))‖ < ε := by
  have happrox : ∀ F : C(UnitAddTorus κ, ℂ), ∃ c : (κ → ℤ) →₀ ℂ,
      ‖F-c.sum (fun k a => a • (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ)))‖ < ε/2 :=
    fun F => unit_torus_fourier_uniform_approximation κ F (ε/2) (by positivity)
  choose c hc using happrox
  obtain ⟨t, _, ht, hcover⟩ := (unit_lipschitz_observables_compact (UnitAddTorus κ)).finite_cover_balls
    (by positivity : 0 < ε/2)
  refine ⟨ht.toFinset.image c, ?_⟩
  intro F hF
  obtain ⟨G, hG⟩ := Set.mem_iUnion.mp (hcover hF)
  obtain ⟨hGt, hball⟩ := Set.mem_iUnion.mp hG
  refine ⟨c G, Finset.mem_image.mpr ⟨G, ht.mem_toFinset.mpr hGt, rfl⟩, ?_⟩
  have hd : ‖F-G‖ < ε/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hball
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using dist_triangle F G _)
    (by linarith only [hd, hc G])

/-- Actual Fourier mode integral under the EXPLICIT normalized product Haar,
independent of any default volume or local MeasureSpace instance. -/
theorem unit_torus_fourier_haar_integral {κ : Type*} [Fintype κ] (k : κ → ℤ) :
    (∫ x : UnitAddTorus κ, UnitAddTorus.mFourier k x
      ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) = if k=0 then 1 else 0 := by
  change (∫ x : κ → UnitAddCircle, ∏ j, fourier (k j) (x j)
    ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)) = _
  rw [integral_fintype_prod_eq_prod]
  by_cases hk : k=0
  · subst k
    simp only [Pi.zero_apply, unit_circle_fourier_haar_integral, ite_true, Finset.prod_const_one]
  · rw [if_neg hk]
    have hex : ∃ j, k j ≠ 0 := by
      by_contra! h
      exact hk (funext h)
    obtain ⟨j, hj⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [unit_circle_fourier_haar_integral, if_neg hj]

end Hindman168
