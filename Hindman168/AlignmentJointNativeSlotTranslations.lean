import Hindman168.AlignmentJointNativeReadings
import Hindman168.AlignmentNativeJointTranslations

/-! The actual native product carries the original slot automorphisms and
product lattice. Their descended maps are continuous in the specified native
metric topology; no numerical Lipschitz bound is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeSlotTranslation (slots : ∀ ν, σ ν → ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ≃*
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G :=
  alignmentNativeJointArrayTranslation (E := fun ν => (D ν).E)
    (I := fun ν => (D ν).I) (G := fun ν => (D ν).G) n v hv slots

theorem alignment_joint_native_slot_translation_lattice (slots : ∀ ν, σ ν → ℤ)
    (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G) :
    alignmentJointNativeSlotTranslation D n v hv slots a ∈
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ ↔
      a ∈ (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ :=
  alignmentNativeJointArrayTranslation_lattice n v hv (fun ν => (D ν).Γ) slots a

noncomputable def alignmentJointNativeCosetSlotTranslation (slots : ∀ ν, σ ν → ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ →
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ :=
  alignmentNativeJointCosetTranslation (E := fun ν => (D ν).E)
    (I := fun ν => (D ν).I) (G := fun ν => (D ν).G) n v hv (fun ν => (D ν).Γ) slots

theorem alignment_joint_native_coset_slot_translation_mk (slots : ∀ ν, σ ν → ℤ)
    (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G) :
    alignmentJointNativeCosetSlotTranslation D n v hv slots (QuotientGroup.mk a)=
      QuotientGroup.mk (alignmentJointNativeSlotTranslation D n v hv slots a) := rfl

theorem alignment_joint_native_coset_slot_translation_continuous (slots : ∀ ν, σ ν → ℤ) :
    Continuous (alignmentJointNativeCosetSlotTranslation D n v hv slots) :=
  alignmentNativeJointCosetTranslation_continuous n v hv (fun ν => (D ν).Γ) slots

theorem alignment_joint_native_metric_coset_slot_translation_continuous (slots : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    Continuous (alignmentJointNativeCosetSlotTranslation D n v hv slots) := by
  dsimp only
  rw [←nativeNilmanifold_metric_topology
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)))]
  exact alignment_joint_native_coset_slot_translation_continuous D n v hv slots

theorem alignment_joint_native_coset_slot_translation_evaluation (slots : ∀ ν, σ ν → ℤ)
    (ν : ι) (z : σ ν → ℤ)
    (y : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    alignmentJointNativeCosetEvaluation D n v hv ν z
      (alignmentJointNativeCosetSlotTranslation D n v hv slots y)=
      alignmentJointNativeCosetEvaluation D n v hv ν (z+slots ν) y := by
  induction y using Quotient.inductionOn with
  | _ a => rfl

end Hindman168
