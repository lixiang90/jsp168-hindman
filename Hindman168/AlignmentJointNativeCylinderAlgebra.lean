import Hindman168.AlignmentJointNativeSlotSeparation
import Hindman168.AlignmentJointMetricReadings

/-! ALL original integer-slot cylinder tests generate a genuine star algebra
on the ACTUAL native array/product quotient. Actual pointwise-lattice slot
separation and compact metric topology prove density in EVERY native test.
No finite-evaluation quotient embedding or numerical projection Lip bound. -/
namespace Hindman168
open scoped Manifold ContDiff Classical NNReal Topology
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeCylinderGenerators :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    Set C(J.G ⧸ J.Γ,ℂ) := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact {f | ∃ (ν : ι) (z : σ ν → ℤ) (obs : C((D ν).G ⧸ (D ν).Γ,ℂ)),
    (∃ K : ℝ≥0, LipschitzWith K obs) ∧ f=alignmentJointNativeMetricReading D n v hv ν z obs}

noncomputable def alignmentJointNativeCylinderTestAlgebra :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    StarSubalgebra ℂ C(J.G ⧸ J.Γ,ℂ) := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact StarAlgebra.adjoin ℂ (alignmentJointNativeCylinderGenerators D n v hv)

theorem alignment_joint_native_cylinder_generators_star :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ f ∈ alignmentJointNativeCylinderGenerators D n v hv,
      star f ∈ alignmentJointNativeCylinderGenerators D n v hv := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  rintro f ⟨ν,z,obs,hobs,rfl⟩
  refine ⟨ν,z,star obs,?_,?_⟩
  · exact (compactLipschitzStarSubalgebra ((D ν).G ⧸ (D ν).Γ)).star_mem' hobs
  · ext y
    rfl

theorem alignment_joint_native_cylinder_algebra_separates :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (alignmentJointNativeCylinderTestAlgebra D n v hv).SeparatesPoints := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro x y hxy
  obtain ⟨ν,z,hz⟩ := alignment_joint_native_distinct_slot_witness D n v hv x y hxy
  obtain ⟨f,⟨obs,hobs,rfl⟩,hneq⟩ := (compact_lipschitz_star_subalgebra_separates ((D ν).G ⧸ (D ν).Γ)) hz
  change ∃ K : ℝ≥0, LipschitzWith K obs at hobs
  let reading := alignmentJointNativeMetricReading D n v hv ν z obs
  have hreading : reading ∈ alignmentJointNativeCylinderTestAlgebra D n v hv :=
    StarAlgebra.subset_adjoin ℂ (alignmentJointNativeCylinderGenerators D n v hv) ⟨ν,z,obs,hobs,rfl⟩
  refine ⟨(reading : J.G ⧸ J.Γ → ℂ),⟨reading,hreading,rfl⟩,?_⟩
  exact hneq

theorem alignment_joint_native_cylinder_uniform_approximation :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∀ (F : C(J.G ⧸ J.Γ,ℂ)) (ε : ℝ), 0 < ε →
      ∃ G ∈ alignmentJointNativeCylinderTestAlgebra D n v hv, ‖F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro F ε hε
  have he := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (alignmentJointNativeCylinderTestAlgebra D n v hv) (alignment_joint_native_cylinder_algebra_separates D n v hv)
  have hf : F ∈ (alignmentJointNativeCylinderTestAlgebra D n v hv).topologicalClosure := by rw [he]; trivial
  change F ∈ closure (alignmentJointNativeCylinderTestAlgebra D n v hv : Set C(J.G ⧸ J.Γ,ℂ)) at hf
  obtain ⟨G,hG,hclose⟩ := Metric.mem_closure_iff.mp hf ε hε
  have hc : dist F G=‖F-G‖ := dist_eq_norm F G
  rw [hc] at hclose
  exact ⟨G,hG,hclose⟩

end Hindman168
