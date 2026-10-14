import Hindman168.AdditiveCopyExactCounts

/-! Exact canonical subsystems for B, BH and BH^2. Target copies are
present once; each retained old copy occurs in one or two root branches.
Their counts are 2^b, 2^b+t and 2^b+2t, t=b*2^(b-1). -/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def rootSmoothedRowEnumeration (b : ℕ) :
    Fin (Fintype.card (RootSmoothedAdditiveCopy b)) → RootSmoothedAdditiveCopy b :=
  (Fintype.equivFin _).symm

noncomputable def rootSmoothedRetainedCopy {b : ℕ} (r : AdditiveNonRootCopy b) (bit : Bool) :
    RootSmoothedAdditiveCopy b := rootSmoothedCopy r.val bit (fun h => (r.property h).elim)

theorem rootSmoothedRetainedCopy_injective (b : ℕ) (bit : Bool) :
    Function.Injective (fun r : AdditiveNonRootCopy b => rootSmoothedRetainedCopy r bit) := by
  intro r s he
  apply Subtype.ext
  exact congrArg (fun q : RootSmoothedAdditiveCopy b => q.val.1) he

theorem rootSmoothedTargetCopy_eq_of_base_none {b : ℕ}
    (r : RootSmoothedAdditiveCopy b) (h : r.val.1.val.1 = none) :
    rootSmoothedTargetCopy r.val.1.val.2 = r := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext h.symm rfl
  · exact (r.property h).symm

noncomputable def rootMomentTarget (b : ℕ) : Finset (Fin (Fintype.card (RootSmoothedAdditiveCopy b))) :=
  Finset.univ.image (fun η : Fin b → Bool =>
    Fintype.equivFin (RootSmoothedAdditiveCopy b) (rootSmoothedTargetCopy η))

noncomputable def rootMomentRetained (b : ℕ) (bit : Bool) :
    Finset (Fin (Fintype.card (RootSmoothedAdditiveCopy b))) :=
  Finset.univ.image (fun r : AdditiveNonRootCopy b =>
    Fintype.equivFin (RootSmoothedAdditiveCopy b) (rootSmoothedRetainedCopy r bit))

noncomputable def rootMomentFirst (b : ℕ) := rootMomentTarget b ∪ rootMomentRetained b false

noncomputable def rootMomentSecond (b : ℕ) := rootMomentFirst b ∪ rootMomentRetained b true

theorem rootMomentTarget_card (b : ℕ) : (rootMomentTarget b).card = 2 ^ b := by
  unfold rootMomentTarget
  have hi : Function.Injective (fun η : Fin b → Bool =>
      Fintype.equivFin (RootSmoothedAdditiveCopy b) (rootSmoothedTargetCopy η)) := by
    intro η θ h
    exact rootSmoothedTargetCopy_injective b ((Fintype.equivFin _).injective h)
  rw [Finset.card_image_of_injective _ hi]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem rootMomentRetained_card (b : ℕ) (bit : Bool) :
    (rootMomentRetained b bit).card = b * 2 ^ (b - 1) := by
  unfold rootMomentRetained
  have hi : Function.Injective (fun r : AdditiveNonRootCopy b =>
      Fintype.equivFin (RootSmoothedAdditiveCopy b) (rootSmoothedRetainedCopy r bit)) := by
    intro r s h
    exact rootSmoothedRetainedCopy_injective b bit ((Fintype.equivFin _).injective h)
  rw [Finset.card_image_of_injective _ hi]
  simp only [Finset.card_univ, additiveNonRootCopy_card]

theorem mem_rootMomentTarget (b : ℕ)
    (u : Fin (Fintype.card (RootSmoothedAdditiveCopy b))) :
    u ∈ rootMomentTarget b ↔ (rootSmoothedRowEnumeration b u).val.1.val.1 = none := by
  constructor
  · intro hu
    obtain ⟨η, _, rfl⟩ := Finset.mem_image.mp hu
    simp only [rootSmoothedRowEnumeration, Equiv.symm_apply_apply, rootSmoothedTargetCopy,
      rootSmoothedCopy, replicaRootCopy]
  · intro hu
    refine Finset.mem_image.mpr ⟨(rootSmoothedRowEnumeration b u).val.1.val.2,
      Finset.mem_univ _, ?_⟩
    rw [rootSmoothedTargetCopy_eq_of_base_none _ hu]
    exact (Fintype.equivFin _).apply_symm_apply u

theorem mem_rootMomentRetained (b : ℕ) (bit : Bool)
    (u : Fin (Fintype.card (RootSmoothedAdditiveCopy b))) :
    u ∈ rootMomentRetained b bit ↔
      (rootSmoothedRowEnumeration b u).val.1.val.1 ≠ none ∧
        (rootSmoothedRowEnumeration b u).val.2 = bit := by
  constructor
  · intro hu
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hu
    simp only [rootSmoothedRowEnumeration, Equiv.symm_apply_apply, rootSmoothedRetainedCopy,
      rootSmoothedCopy]
    exact ⟨r.property, trivial⟩
  · rintro ⟨hb, ht⟩
    let r := rootSmoothedRowEnumeration b u
    have he : rootSmoothedRetainedCopy ⟨r.val.1, hb⟩ bit = r := by
      apply Subtype.ext
      exact Prod.ext rfl ht.symm
    refine Finset.mem_image.mpr ⟨⟨r.val.1, hb⟩, Finset.mem_univ _, ?_⟩
    rw [he]
    exact (Fintype.equivFin _).apply_symm_apply u

theorem rootMomentTarget_retained_disjoint (b : ℕ) (bit : Bool) :
    Disjoint (rootMomentTarget b) (rootMomentRetained b bit) := by
  apply Finset.disjoint_left.mpr
  intro u ht hr
  exact ((mem_rootMomentRetained b bit u).mp hr).1 ((mem_rootMomentTarget b u).mp ht)

theorem rootMomentRetained_disjoint (b : ℕ) :
    Disjoint (rootMomentRetained b false) (rootMomentRetained b true) := by
  apply Finset.disjoint_left.mpr
  intro u h₀ h₁
  have he := ((mem_rootMomentRetained b false u).mp h₀).2.symm.trans
    ((mem_rootMomentRetained b true u).mp h₁).2
  exact Bool.false_ne_true he

theorem rootMomentFirst_card (b : ℕ) :
    (rootMomentFirst b).card = 2 ^ b + b * 2 ^ (b - 1) := by
  rw [rootMomentFirst, Finset.card_union_of_disjoint (rootMomentTarget_retained_disjoint b false),
    rootMomentTarget_card, rootMomentRetained_card]

theorem rootMomentSecond_card (b : ℕ) :
    (rootMomentSecond b).card = 2 ^ b + 2 * (b * 2 ^ (b - 1)) := by
  have hd : Disjoint (rootMomentFirst b) (rootMomentRetained b true) :=
    Finset.disjoint_union_left.mpr
      ⟨rootMomentTarget_retained_disjoint b true, rootMomentRetained_disjoint b⟩
  rw [rootMomentSecond, Finset.card_union_of_disjoint hd, rootMomentFirst_card, rootMomentRetained_card]
  omega

theorem rootMomentSecond_eq_univ (b : ℕ) : rootMomentSecond b = Finset.univ := by
  ext u
  simp only [rootMomentSecond, rootMomentFirst, Finset.mem_union, Finset.mem_univ,
    mem_rootMomentTarget, mem_rootMomentRetained, iff_true]
  by_cases h : (rootSmoothedRowEnumeration b u).val.1.val.1 = none
  · exact Or.inl (Or.inl h)
  · cases (rootSmoothedRowEnumeration b u).val.2 with
    | false => exact Or.inl (Or.inr ⟨h, rfl⟩)
    | true => exact Or.inr ⟨h, rfl⟩

theorem rootSmoothedAdditiveCopy_card (b : ℕ) :
    Fintype.card (RootSmoothedAdditiveCopy b) = 2 ^ b + 2 * (b * 2 ^ (b - 1)) := by
  calc
    _ = Fintype.card (Fin (Fintype.card (RootSmoothedAdditiveCopy b))) := by rw [Fintype.card_fin]
    _ = (rootMomentSecond b).card := by rw [rootMomentSecond_eq_univ, Finset.card_univ]
    _ = _ := rootMomentSecond_card b

end Hindman168
