import Hindman168.AlignmentJointNativeSlotTranslations

/-! The actual native slot translation is a homeomorphism: negating every
slot supplies its inverse. This packages the genuine quotient map already
used by the empirical comparison, rather than assuming invertibility from
continuity. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν + 1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I)
      (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeCosetSlotHomeomorph (slots : ∀ ν, σ ν → ℤ) :
    ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) ≃ₜ
    ((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :=
  alignmentNativeJointCosetTranslationHomeomorph (E := fun ν => (D ν).E)
    (I := fun ν => (D ν).I) (G := fun ν => (D ν).G)
    n v hv (fun ν => (D ν).Γ) slots

@[simp] theorem alignment_joint_native_coset_slot_homeomorph_apply
    (slots : ∀ ν, σ ν → ℤ)
    (x : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    alignmentJointNativeCosetSlotHomeomorph D n v hv slots x =
      alignmentJointNativeCosetSlotTranslation D n v hv slots x := rfl

end Hindman168
