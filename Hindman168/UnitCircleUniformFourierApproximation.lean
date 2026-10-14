import Hindman168.CompactUnitLipschitzObservables
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace Hindman168
open scoped BigOperators Classical Topology

theorem unit_circle_fourier_uniform_approximation (F : C(UnitAddCircle, ℂ))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℤ →₀ ℂ, ‖F-c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))‖ < eps := by
  have hf : F ∈ (Submodule.span ℂ (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  change F ∈ closure ((Submodule.span ℂ
    (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))) : Set C(UnitAddCircle, ℂ)) at hf
  obtain ⟨G, hG, hclose⟩ := Metric.mem_closure_iff.mp hf eps heps
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  exact ⟨c, by simpa only [dist_eq_norm] using hclose⟩

/-- One fixed finite Fourier family approximates every bounded unit Lipschitz
observable. The family is chosen before orbit coefficients and length. -/
theorem unit_circle_finite_uniform_fourier_family (eps : ℝ) (heps : 0 < eps) :
    ∃ A : Finset (ℤ →₀ ℂ), ∀ F ∈ unitLipschitzObservables UnitAddCircle,
      ∃ c ∈ A, ‖F-c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))‖ < eps := by
  have happrox : ∀ F : C(UnitAddCircle, ℂ), ∃ c : ℤ →₀ ℂ,
      ‖F-c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))‖ < eps/2 :=
    fun F => unit_circle_fourier_uniform_approximation F (eps/2) (by positivity)
  choose c hc using happrox
  obtain ⟨t, _, ht, hcover⟩ := (unit_lipschitz_observables_compact UnitAddCircle).finite_cover_balls
    (by positivity : 0 < eps/2)
  refine ⟨ht.toFinset.image c, ?_⟩
  intro F hF
  obtain ⟨G, hG⟩ := Set.mem_iUnion.mp (hcover hF)
  obtain ⟨hGt, hball⟩ := Set.mem_iUnion.mp hG
  refine ⟨c G, Finset.mem_image.mpr ⟨G, ht.mem_toFinset.mpr hGt, rfl⟩, ?_⟩
  have hd : ‖F-G‖ < eps/2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hball
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using dist_triangle F G _)
    (by linarith [hc G])

theorem unit_circle_fourier_haar_integral (k : ℤ) :
    (∫ t : UnitAddCircle, fourier k t ∂AddCircle.haarAddCircle) = if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · simp [hk]
  · rw [if_neg hk]
    exact MeasureTheory.integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hk (by norm_num : (0 : ℝ) < 1))

end Hindman168
