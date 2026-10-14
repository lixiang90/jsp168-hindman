import Hindman168.AlignmentArrayNativeCoordinates
import Hindman168.AlignmentNativeArrayCosetTranslations
import Hindman168.NativeMetricMaskModelTesting

/-! Actual integer-slot evaluation on the constructed native array quotient.
The pointwise lattice makes the evaluation descend; topology compatibility
proves continuity in the supplied native metrics. -/
namespace Hindman168
universe u

variable {σ : Type} {s : ℕ} (D : NativeNilmanifoldData.{u} s)
  (n : ℕ) (v : Fin (n+1) → σ → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))

def alignmentArrayNativeEvaluation (z : σ → ℤ) : (alignmentNativeArrayData D n v hv).G →* D.G := by
  change alignmentNativeAllIntegerArrayGroup (E := D.E) (I := D.I) (G := D.G) n v hv →* D.G
  exact { toFun := fun a => a.val z, map_one' := rfl, map_mul' := fun _ _ => rfl }

noncomputable def alignmentArrayNativeCosetEvaluation (z : σ → ℤ) :
    (alignmentNativeArrayData D n v hv).G ⧸ (alignmentNativeArrayData D n v hv).Γ → D.G ⧸ D.Γ :=
  alignmentNativeArrayCosetEvaluation (E := D.E) (I := D.I) (G := D.G) n v hv D.Γ z

theorem alignment_array_native_coset_evaluation_mk (z : σ → ℤ)
    (a : (alignmentNativeArrayData D n v hv).G) :
    alignmentArrayNativeCosetEvaluation D n v hv z
      (a : (alignmentNativeArrayData D n v hv).G ⧸ (alignmentNativeArrayData D n v hv).Γ) =
      (alignmentArrayNativeEvaluation D n v hv z a : D.G ⧸ D.Γ) := rfl

theorem alignment_array_native_evaluation_value (z : σ → ℤ)
    (a : alignmentNativeAllIntegerArrayGroup (E := D.E) (I := D.I) (G := D.G) n v hv) :
    alignmentArrayNativeEvaluation D n v hv z (alignmentNativeArrayDataValue D n v hv a) = a.val z := rfl

theorem alignment_array_native_coset_evaluation_continuous (z : σ → ℤ) :
    Continuous (alignmentArrayNativeCosetEvaluation D n v hv z) := by
  exact alignmentNativeArrayCosetEvaluation_continuous (E := D.E) (I := D.I) (G := D.G) n v hv D.Γ z

theorem alignment_array_native_metric_coset_evaluation_continuous (z : σ → ℤ) :
    letI := (alignmentNativeArrayData D n v hv).metric
    letI : TopologicalSpace ((alignmentNativeArrayData D n v hv).G ⧸ (alignmentNativeArrayData D n v hv).Γ) :=
      (alignmentNativeArrayData D n v hv).metric.toUniformSpace.toTopologicalSpace
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (alignmentArrayNativeCosetEvaluation D n v hv z) := by
  rw [←nativeNilmanifold_metric_topology (alignmentNativeArrayData D n v hv),←nativeNilmanifold_metric_topology D]
  exact alignment_array_native_coset_evaluation_continuous D n v hv z

end Hindman168
