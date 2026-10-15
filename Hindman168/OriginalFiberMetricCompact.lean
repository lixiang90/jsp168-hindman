import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! A compactness reduction for the fibre metric problem. The local
lower distance bounds remain explicit hypotheses of this general lemma;
they will be supplied by the actual BCH quotient coordinate charts. -/

namespace Hindman168.OriginalFiberMetric
open Set Filter Topology
open scoped NNReal

theorem local_lower_of_open_parameterization
    {E X Y : Type*} [TopologicalSpace E] [MetricSpace X] [MetricSpace Y]
    (q : E → X) (f : X → Y) (hq : IsOpenMap q) {V : Set E}
    (hV : IsOpen V) {u : E} (hu : u ∈ V) {C : ℝ≥0}
    (hbound : ∀ v ∈ V, ∀ w ∈ V,
      dist (q v) (q w) ≤ C * dist (f (q v)) (f (q w))) :
    ∃ U ∈ 𝓝 (q u), ∀ x ∈ U, ∀ y ∈ U,
      dist x y ≤ C * dist (f x) (f y) := by
  refine ⟨q '' V, (hq V hV).mem_nhds ⟨u, hu, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  exact hbound v hv w hw

theorem exists_antilipschitz_of_compact_local
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y) (hf : Continuous f) (hinj : Function.Injective f)
    (hloc : ∀ x : X, ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ z ∈ U, dist y z ≤ C * dist (f y) (f z)) :
    ∃ C : ℝ≥0, AntilipschitzWith C f := by
  let e : X ≃ₜ Set.range f := (hf.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  letI : CompactSpace (Set.range f) := e.compactSpace
  have he (y : Set.range f) : f (e.symm y) = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hlocal : LocallyLipschitz e.symm := by
    intro y
    obtain ⟨C, U, hU, hCU⟩ := hloc (e.symm y)
    refine ⟨C, e.symm ⁻¹' U, e.symm.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simpa only [he, Subtype.dist_eq] using hCU (e.symm a) ha (e.symm b) hb
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := Set.univ) isCompact_univ hlocal.locallyLipschitzOn
  refine ⟨C, AntilipschitzWith.of_le_mul_dist ?_⟩
  intro x y
  have h := hC.dist_le_mul (e x) (Set.mem_univ _) (e y) (Set.mem_univ _)
  have heval (a : X) : (e a).val = f a := rfl
  simpa only [Homeomorph.symm_apply_apply, Subtype.dist_eq, heval] using h

end Hindman168.OriginalFiberMetric
