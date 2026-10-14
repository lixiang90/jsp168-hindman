import Hindman168.PositivePrincipalSumFutureNative

namespace Hindman168
open scoped BigOperators Classical

noncomputable def principalNativeScaleObservation {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (i : Fin n) :
    Finset (Fin n) → ℚ → Multiplicative (AlignmentAddingPair M
      (principalAlignmentEmbedding e heM i) → ℤ) → (Fin r → ℝ) :=
  fun B a u κ => if ha : a ∈ A then S (B.erase i) i (⟨a,ha⟩,κ) w
    (alignmentIntegerArrayArgument x (F.modulus w)
      (fun p => alignmentPairResidue q₀ w (F.modulus w) p x)
      (fun p => alignmentPairProgression q₀ w (F.modulus w) p x)
      ((B.erase i).image (principalAlignmentEmbedding e heM))
      (x (selectedPrincipalIndex e heM i)) u.toAdd u.toAdd) else 0

/-- Canonical requests for the single scale-aware palette specialize to
all the color models for any selected b, with no change of palette after b. -/
theorem principal_native_scale_thresholds_specialize {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (hclosed : FiniteScaleClosure B A)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (θ : ℝ) (b : B) (i : Fin n)
    (hreq : ∀ request ∈ alignmentCanonicalRequests n i,
      principalThresholdRequestHolds q₀ b.val
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeScaleObservation e heM F A S q₀ w x i) θ 1 request) :
    ∀ κ : Fin r, ∀ request ∈ alignmentCanonicalRequests n i,
      principalThresholdRequestHolds q₀ b.val
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeInputObservation e heM F q₀ w x
          (fun T i => S T i (scaleBlockColorIndex B A hclosed b.val b.property
            (insert i T) (Finset.insert_nonempty _ _) κ) w) i) θ 1 request := by
  intro κ request hr
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hr
  have hh := hreq _ (List.mem_map.mpr ⟨T,hT,rfl⟩)
  change ∀ a ∈ ({1} : Finset ℚ), ∀ word ∈ alignmentTerminalWords
    (alignmentCanonicalTargetPairs n i T.val), _ at hh ⊢
  intro a ha word hw k
  have ha1 : a = 1 := Finset.mem_singleton.mp ha
  subst a
  have h := hh 1 (Finset.mem_singleton_self _) word hw κ
  have hi : i ∉ T.val := fun hi => (lt_irrefl i)
    (alignmentCanonicalTargetTails_before T.val T.property i hi)
  have hmem := hclosed b.val b.property (insert i T.val) (Finset.insert_nonempty _ _)
  simpa only [one_mul, principalNativeScaleObservation, principalNativeInputObservation,
    alignmentCanonicalRequest, alignmentTerminalRequest, Finset.erase_insert hi,
    dif_pos hmem, scaleBlockColorIndex] using h

end Hindman168
