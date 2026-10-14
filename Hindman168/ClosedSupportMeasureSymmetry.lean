import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Homeomorph.Defs

/-! Equality of actual measures yields setwise invariance of their closed full support. -/
namespace Hindman168
open Set MeasureTheory

theorem closed_support_measure_mapsTo {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) (K : Set Y) (hK : IsClosed K)
    (hsupport : ∀ U : Set Y, IsOpen U → (0 < μ U ↔ (U ∩ K).Nonempty))
    (T : Y → Y) (hT : Continuous T) (hinv : Measure.map T μ = μ) : MapsTo T K K := by
  intro x hx
  by_contra hnot
  have hzero : μ Kᶜ = 0 := by
    have hn : ¬ 0 < μ Kᶜ := by
      rw [hsupport Kᶜ hK.isOpen_compl]
      rintro ⟨y,hy,hyK⟩
      exact hy hyK
    exact le_antisymm (le_of_not_gt hn) bot_le
  have hpos : 0 < μ (T ⁻¹' Kᶜ) :=
    (hsupport _ (hK.isOpen_compl.preimage hT)).mpr ⟨x,hnot,hx⟩
  have he : μ (T ⁻¹' Kᶜ) = μ Kᶜ := by
    rw [← Measure.map_apply hT.measurable hK.isOpen_compl.measurableSet,hinv]
  exact hpos.ne' (he.trans hzero)

theorem closed_support_homeomorph_invariant {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) (K : Set Y) (hK : IsClosed K)
    (hsupport : ∀ U : Set Y, IsOpen U → (0 < μ U ↔ (U ∩ K).Nonempty))
    (T : Y ≃ₜ Y) (hinv : Measure.map T μ = μ) : T '' K = K := by
  have hi : Measure.map T.symm μ = μ := by
    calc
      _ = Measure.map T.symm (Measure.map T μ) := congrArg (Measure.map T.symm) hinv.symm
      _ = μ := by
        rw [Measure.map_map T.symm.continuous.measurable T.continuous.measurable]
        simp only [Function.comp_def,T.symm_apply_apply]
        exact Measure.map_id
  apply subset_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact closed_support_measure_mapsTo μ K hK hsupport T T.continuous hinv hx
  · intro y hy
    exact ⟨T.symm y,closed_support_measure_mapsTo μ K hK hsupport T.symm T.symm.continuous hi hy,
      T.apply_symm_apply y⟩

end Hindman168
