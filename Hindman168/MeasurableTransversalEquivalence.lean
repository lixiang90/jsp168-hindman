import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Actual continuous bijective restriction to a measurable transversal
has a genuinely measurable inverse; no continuous selector is assumed. -/

namespace Hindman168
open Set MeasureTheory

noncomputable def measurableTransversalEquiv {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : Continuous f) (F : Set X) (hF : MeasurableSet F)
    (hinj : F.InjOn f) (hcover : ∀ y, ∃ x ∈ F, f x = y) : F ≃ᵐ Y := by
  let e : F ≃ Y := Equiv.ofBijective (F.restrict f) ⟨injOn_iff_injective.mp hinj, by
    intro y
    obtain ⟨x, hx, he⟩ := hcover y
    exact ⟨⟨x,hx⟩, he⟩⟩
  have hm := ContinuousOn.measurableEmbedding hF hf.continuousOn hinj
  exact { e with
    measurable_toFun := hm.measurable
    measurable_invFun := hm.measurable_comp_iff.mp (by
      have he : F.restrict f ∘ e.symm = id := funext e.apply_symm_apply
      rw [he]
      exact measurable_id) }

end Hindman168
