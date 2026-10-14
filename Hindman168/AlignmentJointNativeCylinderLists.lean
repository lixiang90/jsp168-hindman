import Hindman168.AlignmentJointNativeCylinderAlgebra
import Hindman168.ContinuousCylinderListRepresentation

/-! Finite ORIGINAL slot/observer cylinder lists approximate EVERY actual
native quotient test. Compact full numerical families have ONE fixed finite
approximant list before original source/box/residue/sample choices. -/
namespace Hindman168
open scoped Manifold ContDiff Classical NNReal Topology
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_joint_native_cylinder_list_representation :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∀ F ∈ alignmentJointNativeCylinderTestAlgebra D n v hv,
      ∃ l : List (ℂ × List C(J.G ⧸ J.Γ,ℂ)),
        (∀ t ∈ l, ∀ f ∈ t.2, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
        F=continuousCylinderLinearCombination l := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro F hF
  exact continuous_star_cylinder_list_representation (alignmentJointNativeCylinderGenerators D n v hv)
    (alignment_joint_native_cylinder_generators_star D n v hv) F hF

theorem alignment_joint_native_cylinder_list_approximation :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∀ (F : C(J.G ⧸ J.Γ,ℂ)) (ε : ℝ), 0 < ε →
      ∃ l : List (ℂ × List C(J.G ⧸ J.Γ,ℂ)),
        (∀ t ∈ l, ∀ f ∈ t.2, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
        ‖F-continuousCylinderLinearCombination l‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro F ε hε
  obtain ⟨G,hG,hclose⟩ := alignment_joint_native_cylinder_uniform_approximation D n v hv F ε hε
  obtain ⟨l,hl,rfl⟩ := alignment_joint_native_cylinder_list_representation D n v hv G hG
  exact ⟨l,hl,hclose⟩

theorem alignment_joint_native_compact_cylinder_approximation :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∀ (H : Set C(J.G ⧸ J.Γ,ℂ)), IsCompact H → ∀ ε : ℝ, 0 < ε →
      ∃ P : Finset C(J.G ⧸ J.Γ,ℂ),
        (∀ G ∈ P, G ∈ alignmentJointNativeCylinderTestAlgebra D n v hv) ∧
        ∀ F ∈ H, ∃ G ∈ P, ‖F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  intro H hH ε hε
  have ha : ∀ F : C(J.G ⧸ J.Γ,ℂ), ∃ G ∈ alignmentJointNativeCylinderTestAlgebra D n v hv,
      ‖F-G‖ < ε/2 := fun F => alignment_joint_native_cylinder_uniform_approximation D n v hv F (ε/2) (by positivity)
  choose G hG hclose using ha
  obtain ⟨t,_,ht,hcover⟩ := hH.finite_cover_balls (by positivity : 0 < ε/2)
  refine ⟨ht.toFinset.image G,?_,?_⟩
  · intro K hK
    obtain ⟨F,_,rfl⟩ := Finset.mem_image.mp hK
    exact hG F
  · intro F hF
    obtain ⟨K,hK⟩ := Set.mem_iUnion.mp (hcover hF)
    obtain ⟨hKt,hball⟩ := Set.mem_iUnion.mp hK
    refine ⟨G K,Finset.mem_image.mpr ⟨K,ht.mem_toFinset.mpr hKt,rfl⟩,?_⟩
    have hd : ‖F-K‖ < ε/2 := by
      have hc : dist F K=‖F-K‖ := dist_eq_norm F K
      rw [Metric.mem_ball,hc] at hball
      exact hball
    have htri := norm_sub_le_norm_sub_add_norm_sub F K (G K)
    linarith only [hd,hclose K,htri]

end Hindman168
