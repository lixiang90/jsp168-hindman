import Hindman168.AlignmentJointNativeCylinderAlgebra
import Hindman168.AlignmentJointNativeSlotTranslations
import Hindman168.AlignmentNativeCanonicalCubeArray
import Mathlib.Algebra.BigOperators.Fin

/-! Every cylinder list has an exact finite duplicated-component presentation
with its ORIGINAL slot observers and legitimate numerical bounds. Repeated
components and empty lists are retained before any source or sample choice. -/
namespace Hindman168
open scoped Manifold ContDiff Classical NNReal Topology BigOperators
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_native_cylinder_list_original_presentation :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ (l : List C(J.G ⧸ J.Γ,ℂ)),
      (∀ f ∈ l, f ∈ alignmentJointNativeCylinderGenerators D n v hv) →
      ∃ (label : Fin l.length → ι) (slot : ∀ j, σ (label j) → ℤ)
        (obs : ∀ j, C((D (label j)).G ⧸ (D (label j)).Γ,ℂ))
        (B : Fin l.length → ℝ) (L : Fin l.length → NNReal),
        (∀ j, 0 < B j ∧ obs j ∈ boundedComplexLipschitzObservables
          ((D (label j)).G ⧸ (D (label j)).Γ) (B j) (L j)) ∧
        ∀ x : J.G ⧸ J.Γ, l.prod x =
          ∏ j, obs j (alignmentJointNativeCosetEvaluation D n v hv (label j) (slot j) x) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro l hl
  have hget (j : Fin l.length) : ∃ (ν : ι) (z : σ ν → ℤ)
      (obs : C((D ν).G ⧸ (D ν).Γ,ℂ)) (K : NNReal),
      LipschitzWith K obs ∧ l[j.val]=alignmentJointNativeMetricReading D n v hv ν z obs := by
    obtain ⟨ν,z,obs,⟨K,hK⟩,he⟩ := hl l[j.val] (List.getElem_mem j.isLt)
    exact ⟨ν,z,obs,K,hK,he⟩
  choose label slot obs L hL he using hget
  refine ⟨label,slot,obs,(fun j => ‖obs j‖+1),L,?_,?_⟩
  · intro j
    refine ⟨by positivity,hL j,?_⟩
    intro x
    exact (ContinuousMap.norm_coe_le_norm (obs j) x).trans (by linarith)
  · intro x
    rw [←Fin.prod_univ_getElem l,ContinuousMap.prod_apply]
    apply Finset.prod_congr rfl
    intro j _
    rw [he j]
    rfl

end Hindman168
