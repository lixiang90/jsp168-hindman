import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! A genuine continuous parameter family freezes uniformly over a compact
fiber. The sequence threshold follows selection of a positive locality
radius, preserving the required length-before-locality limit order. -/
namespace Hindman168
open Filter Set
open scoped Topology

theorem compact_sequential_parameter_freezing {P X Y : Type*}
    [UniformSpace P] [WeaklyLocallyCompactSpace P]
    [UniformSpace X] [CompactSpace X] [PseudoMetricSpace Y]
    (F : (P × ℝ) × X → Y) (hF : Continuous F)
    (theta : ℕ → P) (a : P) (htheta : Tendsto theta atTop (𝓝 a))
    (beta ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop, ∀ t : ℝ, |t-beta| < r →
      ∀ x : X, dist (F ((theta n,t),x)) (F ((a,beta),x)) < ε := by
  have hu := Continuous.tendstoUniformly (fun p : P × ℝ => fun x : X => F (p,x)) hF (a,beta)
  have he := (Metric.tendstoUniformly_iff.mp hu) ε hε
  rw [nhds_prod_eq] at he
  obtain ⟨U,hU,V,hV,hUV⟩ := Filter.mem_prod_iff.mp he
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r,hr,?_⟩
  filter_upwards [htheta.eventually hU] with n hn
  intro t ht x
  have htV : t ∈ V := hBall (by simpa only [Metric.mem_ball, Real.dist_eq] using ht)
  have h := hUV (show (theta n,t) ∈ U ×ˢ V from ⟨hn,htV⟩) x
  simpa only [dist_comm] using h

end Hindman168
