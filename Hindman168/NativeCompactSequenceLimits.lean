import Hindman168.NativeSubgroupCompactNormalization

/-! Genuine compact native group subsequences, pulled through the ACTUAL
global exponential homeomorphism to the original real model. No extra
metrization or first-countability of an arbitrary topological group is assumed. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_compact_sequence_limit {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (K : Set D.G) (hK : IsCompact K)
    (c : ℕ → D.G) (hc : ∀ n, c n ∈ K) :
    ∃ a : D.G, a ∈ K ∧ ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (c ∘ f) atTop (𝓝 a) := by
  let e : D.E ≃ₜ D.G := nativeLieGlobalExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G)
  have hlogK : IsCompact (e.symm '' K) := hK.image e.symm.continuous
  have hx : ∀ n, e.symm (c n) ∈ e.symm '' K := fun n => ⟨c n,hc n,rfl⟩
  obtain ⟨z,hz,f,hf,hlim⟩ := hlogK.tendsto_subseq hx
  obtain ⟨a,ha,haz⟩ := hz
  subst z
  refine ⟨a,ha,f,hf,?_⟩
  have he := (e.continuous.tendsto (e.symm a)).comp hlim
  simpa only [Function.comp_def, e.apply_symm_apply] using he

end Hindman168
