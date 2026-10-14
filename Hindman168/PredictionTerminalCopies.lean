import Hindman168.MasterCopiedReplicaCubeMajorant

/-!
# Every canonical root copy and retained prediction copy

The finite row enumeration is bijective, so the full-family application
has no row-injectivity premise. Root indices contain exactly all 2^h
branch choices. Retained indices contain every canonical nonroot copy;
zero-response branches were already removed in the row type.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

noncomputable def copiedPredictionRowEnumeration {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) :
    Fin (Fintype.card (CopiedReplicaCubeRow dir)) → CopiedReplicaCubeRow dir :=
  (Fintype.equivFin (CopiedReplicaCubeRow dir)).symm

theorem copiedPredictionRowEnumeration_injective {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : Function.Injective (copiedPredictionRowEnumeration dir) :=
  (Fintype.equivFin (CopiedReplicaCubeRow dir)).symm.injective

noncomputable def copiedPredictionRootIndices {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : Finset (Fin (Fintype.card (CopiedReplicaCubeRow dir))) :=
  Finset.univ.image (fun η : Fin h → Bool =>
    Fintype.equivFin (CopiedReplicaCubeRow dir) (replicaRootCopy dir η))

noncomputable def copiedPredictionRetainedIndices {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : Finset (Fin (Fintype.card (CopiedReplicaCubeRow dir))) :=
  Finset.univ.filter (fun u => (copiedPredictionRowEnumeration dir u).val.1 ≠ none)

theorem copiedPredictionRootIndices_nonempty {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : (copiedPredictionRootIndices dir).Nonempty := by
  apply Finset.image_nonempty.mpr
  exact ⟨(fun _ => false), Finset.mem_univ _⟩

theorem copiedPredictionRootIndices_card {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : (copiedPredictionRootIndices dir).card = 2 ^ h := by
  unfold copiedPredictionRootIndices
  have hinj : Function.Injective (fun η : Fin h → Bool =>
      Fintype.equivFin (CopiedReplicaCubeRow dir) (replicaRootCopy dir η)) :=
    (Fintype.equivFin (CopiedReplicaCubeRow dir)).injective.comp (replicaRootCopy_injective dir)
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem mem_copiedPredictionRootIndices {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (u : Fin (Fintype.card (CopiedReplicaCubeRow dir))) :
    u ∈ copiedPredictionRootIndices dir ↔ (copiedPredictionRowEnumeration dir u).val.1 = none := by
  constructor
  · intro hu
    obtain ⟨η, _, rfl⟩ := Finset.mem_image.mp hu
    simp only [copiedPredictionRowEnumeration, Equiv.symm_apply_apply, replicaRootCopy]
  · intro hu
    have he : replicaRootCopy dir (copiedPredictionRowEnumeration dir u).val.2 =
        copiedPredictionRowEnumeration dir u := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact hu.symm
      · rfl
    apply Finset.mem_image.mpr
    refine ⟨(copiedPredictionRowEnumeration dir u).val.2, Finset.mem_univ _, ?_⟩
    rw [he]
    exact (Fintype.equivFin (CopiedReplicaCubeRow dir)).apply_symm_apply u

theorem copiedPredictionRootRetained_disjoint {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) :
    Disjoint (copiedPredictionRootIndices dir) (copiedPredictionRetainedIndices dir) := by
  apply Finset.disjoint_left.mpr
  intro u hu hr
  exact (Finset.mem_filter.mp hr).2 ((mem_copiedPredictionRootIndices dir u).mp hu)

theorem copiedPredictionRootRetained_union {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) :
    copiedPredictionRootIndices dir ∪ copiedPredictionRetainedIndices dir = Finset.univ := by
  ext u
  simp only [Finset.mem_union, mem_copiedPredictionRootIndices, copiedPredictionRetainedIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(fun _ => True.intro), (fun _ => eq_or_ne _ _)⟩

noncomputable def allPredictionCubeDirections (b d : ℕ) :
    Fin (Fintype.card (Fin b × CubeVertex d)) → Fin b × CubeVertex d :=
  (Fintype.equivFin (Fin b × CubeVertex d)).symm

theorem allPredictionCubeDirections_bijective (b d : ℕ) :
    Function.Bijective (allPredictionCubeDirections b d) :=
  (Fintype.equivFin (Fin b × CubeVertex d)).symm.bijective

theorem allPredictionCubeDirections_unique_zero {b d : ℕ}
    (v : Fin b × CubeVertex d) (i : Fin (Fintype.card (Fin b × CubeVertex d))) :
    replicaCubeResponseConstant (allPredictionCubeDirections b d i).1
      (allPredictionCubeDirections b d i).2 (some v) = 0 ↔
      i = Fintype.equivFin (Fin b × CubeVertex d) v := by
  rw [replicaCubeResponseConstant_zero_iff, Option.some.injEq]
  change v = (Fintype.equivFin (Fin b × CubeVertex d)).symm i ↔ _
  exact (Equiv.eq_symm_apply _).trans eq_comm

theorem MasterParameterConditions.all_copied_prediction_terminal_tendsto
    {n N m r b d h L : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → Fin (Fintype.card (CopiedReplicaCubeRow dir)) → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ u, tailBound ((C w).tailCutoffs (F.cutoff w) (label w u)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    Tendsto (fun w => conditionalFiniteAverage
      (masterPrimeSlotsMass F w (fun j => gap w j))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => (∏ u ∈ copiedPredictionRootIndices dir,
          (masterCopiedPredictionCubeWeight F C label s f dir
            (fun _ => copiedPredictionRowEnumeration dir) w u x y - 1)) *
        ∏ u ∈ copiedPredictionRetainedIndices dir,
          (1 + masterCopiedPredictionCubeWeight F C label s f dir
            (fun _ => copiedPredictionRowEnumeration dir) w u x y)))
      atTop (𝓝 0) := by
  exact hF.copied_replica_cube_centered_majorant_tendsto C hN label gap V hV
    hdivbudget hprimebudget T hT s e hs f hf dir
    (fun _ => copiedPredictionRowEnumeration dir)
    (Eventually.of_forall (fun _ => copiedPredictionRowEnumeration_injective dir))
    H index Tmin loc len E hharmbudget hlengthgrowth hlen
    (copiedPredictionRootIndices dir) (copiedPredictionRetainedIndices dir)
    (copiedPredictionRootRetained_disjoint dir) (copiedPredictionRootIndices_nonempty dir)

end Hindman168
