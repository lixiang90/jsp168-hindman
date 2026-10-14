import Hindman168.AlignmentSelectedAllTargetsCosets

/-! A concrete countable catalogue containing every complete marginal cube.
Each entry consists of an earlier target tail and a dimension. Its slots
are all factors with that target, duplicated at EVERY cube vertex. This
catalogue can be supplied to the same-source all-target selection theorem. -/
namespace Hindman168
open scoped Classical

abbrev AlignmentPriorTail (N : ℕ) (i : Fin N) :=
  {T : Finset (Fin N) // ∀ j ∈ T, j < i}

noncomputable def alignmentDuplicatedTargetCode {N : ℕ} (i : Fin N) (τ : ℕ) :
    AlignmentPriorTail N i × ℕ :=
  (Encodable.decode (α := AlignmentPriorTail N i × ℕ) τ).getD
    (⟨∅, by simp⟩, 0)

 theorem alignment_duplicated_target_code_encode {N : ℕ} (i : Fin N)
    (T : AlignmentPriorTail N i) (d : ℕ) :
    alignmentDuplicatedTargetCode i (Encodable.encode (T,d)) = (T,d) := by
  simp [alignmentDuplicatedTargetCode]

 theorem alignment_duplicated_target_code_surjective {N : ℕ} (i : Fin N) :
    Function.Surjective (alignmentDuplicatedTargetCode i) := by
  rintro ⟨T,d⟩
  exact ⟨Encodable.encode (T,d), alignment_duplicated_target_code_encode i T d⟩

abbrev AlignmentDuplicatedTargetSlots {ι : Type} {N : ℕ} (i : Fin N)
    (targets : ι → Finset (Fin N)) (c : AlignmentPriorTail N i × ℕ) :=
  {ν : ι // targets ν = c.1.val} × Finset (Fin c.2)

noncomputable def alignmentDuplicatedTargetIndex {ι : Type} {N : ℕ} (i : Fin N)
    (targets : ι → Finset (Fin N)) (c : AlignmentPriorTail N i × ℕ) :
    AlignmentDuplicatedTargetSlots i targets c → ι := fun a => a.1.val

 theorem alignment_duplicated_target_uniform {ι : Type} {N : ℕ} (i : Fin N)
    (targets : ι → Finset (Fin N)) (c : AlignmentPriorTail N i × ℕ) :
    targets ∘ alignmentDuplicatedTargetIndex i targets c = fun _ => c.1.val := by
  funext a
  exact a.1.property

 theorem alignment_duplicated_target_before {N : ℕ} (i : Fin N) (τ : ℕ) :
    ∀ j ∈ (alignmentDuplicatedTargetCode i τ).1.val, j < i :=
  (alignmentDuplicatedTargetCode i τ).1.property

/-- Dependent geometric assertions can be proved on this natural-number
catalogue and then recovered for any particular full marginal cube. -/
theorem alignment_duplicated_catalogue_forall {N : ℕ} (i : Fin N)
    (P : AlignmentPriorTail N i × ℕ → Prop)
    (h : ∀ τ, P (alignmentDuplicatedTargetCode i τ)) : ∀ c, P c := by
  intro c
  obtain ⟨τ, rfl⟩ := alignment_duplicated_target_code_surjective i c
  exact h τ

end Hindman168
