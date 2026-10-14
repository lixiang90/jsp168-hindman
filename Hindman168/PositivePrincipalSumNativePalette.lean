import Hindman168.PositivePrincipalSumNativeAdapter
import Hindman168.PositivePrincipalSumEvents

/-! The existing finite-word palette requirement implies the concrete
principal alignment event, through the original native integer arguments. -/
namespace Hindman168
open scoped BigOperators Classical

noncomputable def principalNativeLetter {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (p : AlignmentAddingPair n i) :
    Multiplicative (AlignmentAddingPair M (f i) → ℤ) :=
  Multiplicative.ofAdd (alignmentAuxiliaryUnit (p.map f) 1)

theorem principal_native_word_slots {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (q₀ : ℕ) (b : Fin n → ℚ)
    (L : List (AlignmentAddingPair n i)) :
    (alignmentWordValue q₀ b (principalNativeLetter f) (L.map (fun p => (p, (1 : ℚ))))).toAdd =
      (L.map (fun p => alignmentAuxiliaryUnit (p.map f)
        ⌊(q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
          finiteScaleBlockProduct b (alignmentPairTargetBlock p))⌋)).sum := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, alignmentWordValue, toAdd_mul, toAdd_zpow, ih,
      List.sum_cons, principalNativeLetter, toAdd_ofAdd,
      alignmentLetterScalar, one_mul]
    congr 1
    funext j
    simp [alignmentAuxiliaryUnit, Pi.smul_apply]

noncomputable def principalNativeInputPalette {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → Fin n → ℤ → ℝ) (θ : ℝ) (i : Fin n) :
    Finset (Fin n) → ℚ → Multiplicative (AlignmentAddingPair M
      (principalAlignmentEmbedding e heM i) → ℤ) → Bool :=
  fun B _ u => decide (θ < S (B.erase i) i
    (alignmentIntegerArrayArgument x (F.modulus w)
      (fun p => alignmentPairResidue q₀ w (F.modulus w) p x)
      (fun p => alignmentPairProgression q₀ w (F.modulus w) p x)
      ((B.erase i).image (principalAlignmentEmbedding e heM))
      (x (selectedPrincipalIndex e heM i)) u.toAdd u.toAdd))

/-- This is an adapter from the existing canonical-request predicate, not
an assumed equivalence of alignment events. The requests use the original
integer array palette and the original denominator-cleared word exponents. -/
theorem principal_adding_alignment_of_native_requests
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (b : Fin n → ℚ) (hb : ∀ k, 0 < b k)
    (S : Finset (Fin n) → Fin n → ℤ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hclear : ∀ i, ∀ p : AlignmentAddingPair n i,
      (q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) ∈ (Int.castRingHom ℚ).range)
    (hratio : ∀ i, ∀ p : AlignmentAddingPair n i,
      ((principalBlockCoefficient M e p.sourceTail p.sourcePivot
        (finiteScaleBlockProduct b (alignmentPairSourceBlock p)) w /
        principalBlockCoefficient M e p.targetTail i
        (finiteScaleBlockProduct b (alignmentPairTargetBlock p)) w : ℕ) : ℚ) =
      ((selectedSubsetScale M e w (alignmentPairSourceBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairSourceBlock p)) /
      ((selectedSubsetScale M e w (alignmentPairTargetBlock p) : ℚ) *
          finiteScaleBlockProduct b (alignmentPairTargetBlock p)))
    (hreq : ∀ i, ∀ request ∈ alignmentCanonicalRequests n i,
      alignmentPivotRequestHolds q₀ b
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeInputPalette e heM F q₀ w x S θ i) 1 request) :
    PrincipalAddingAlignment M e b w S θ (fun k => x (selectedPrincipalIndex e heM k)) := by
  intro T i hT hbefore D htarget hcenter
  let f := principalAlignmentEmbedding e heM
  let z := fun p : AlignmentAddingPair n i =>
    ⌊(q₀ : ℚ) * (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
      finiteScaleBlockProduct b (alignmentPairTargetBlock p))⌋
  have hz (p : AlignmentAddingPair n i) : (z p : ℚ) = (q₀ : ℚ) *
      (finiteScaleBlockProduct b (alignmentPairSourceBlock p) /
        finiteScaleBlockProduct b (alignmentPairTargetBlock p)) := by
    obtain ⟨k, hk⟩ := hclear i p
    change (⌊_⌋ : ℚ) = _
    rw [← hk]
    simp
  by_cases hD : D.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hD
    have htcanon : T ∈ alignmentCanonicalTargetTails n i :=
      (htarget p₀ hp₀) ▸ alignmentCanonicalTargetTails_contains p₀
    let ordered := alignmentCanonicalTargetPairs n i T
    let selected := ordered.filter (fun p => p ∈ D)
    have hsubset : D ⊆ ordered.toFinset := by
      intro p hp
      exact List.mem_toFinset.mpr ((alignmentCanonicalTargetPairs_contains T p).mpr (htarget p hp))
    have hsupport : selected.toFinset = D :=
      alignmentTerminalWords_filter_support ordered D hsubset
    have hnodup : selected.Nodup := (alignmentCanonicalTargetPairs_nodup n i T).filter _
    have hslots : (alignmentWordValue q₀ b (principalNativeLetter f)
        (selected.map (fun p => (p, (1 : ℚ))))).toAdd =
        ∑ p ∈ D, alignmentAuxiliaryUnit (p.map f) (z p) := by
      rw [principal_native_word_slots, ← List.sum_toFinset _ hnodup, hsupport]
    have hc := alignmentCanonicalRequests_comparison q₀ b (principalNativeLetter f)
      (principalNativeInputPalette e heM F q₀ w x S θ i) 1 (hreq i) T htcanon
      selected List.filter_sublist
    have hi : i ∉ T := fun hi => (lt_irrefl i) (hbefore i hi)
    simp only [principalNativeInputPalette, Finset.erase_insert hi, smul_eq_mul,
      mul_one, toAdd_one, hslots] at hc
    have harg := principal_native_array_argument_sum hF e heM hq hw x hx T i hbefore D
      htarget b hb z (fun p _ => hz p) (fun p _ => hratio i p)
    dsimp only at harg
    simp only [f, principalAlignmentEmbedding, OrderEmbedding.coe_ofStrictMono] at harg hc
    rw [harg] at hc
    have hbase := principal_native_array_argument_sum hF e heM hq hw x hx T i hbefore ∅
      (by simp) b hb z (by simp) (by simp)
    simp only [Finset.sum_empty, add_zero] at hbase
    simp only [principalAlignmentEmbedding, OrderEmbedding.coe_ofStrictMono] at hbase
    simp only [hbase] at hc
    have hgood : θ < S T i (principalSubsetProduct (insert i T)
        (fun k => x (selectedPrincipalIndex e heM k))) := by linarith
    have hleft : decide (θ < S T i (principalSubsetProduct (insert i T)
        (fun k => x (selectedPrincipalIndex e heM k)))) = true := by simpa using hgood
    have hout := of_decide_eq_true (hc.symm.trans hleft)
    simpa only [finiteScaleBlockProduct, f, principalAlignmentEmbedding,
      OrderEmbedding.coe_ofStrictMono] using hout
  · have hempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp only [hempty, Finset.sum_empty, add_zero]
    linarith

/-- One palette is fixed before choosing the scale vector. Its finite color
space is `Fin r → Bool`, independent of the threshold and model complexity. -/
noncomputable def principalNativeScalePalette {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (A : Finset ℚ)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (θ : ℝ) (i : Fin n) :
    Finset (Fin n) → ℚ → Multiplicative (AlignmentAddingPair M
      (principalAlignmentEmbedding e heM i) → ℤ) → (Fin r → Bool) :=
  fun B a u κ => if ha : a ∈ A then decide (θ < S (B.erase i) i (⟨a,ha⟩,κ) w
    (alignmentIntegerArrayArgument x (F.modulus w)
      (fun p => alignmentPairResidue q₀ w (F.modulus w) p x)
      (fun p => alignmentPairProgression q₀ w (F.modulus w) p x)
      ((B.erase i).image (principalAlignmentEmbedding e heM))
      (x (selectedPrincipalIndex e heM i)) u.toAdd u.toAdd)) else false

/-- Canonical requests for the single scale-aware palette specialize to
all the color models for any selected b, with no change of palette after b. -/
theorem principal_native_scale_requests_specialize {n M r : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (F : MasterParameterFamily)
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (hclosed : FiniteScaleClosure B A)
    (S : Finset (Fin n) → Fin n → ScaleColorIndex A r → ℕ → ℤ → ℝ)
    (q₀ w : ℕ) (x : Fin M → ℕ) (θ : ℝ) (b : B) (i : Fin n)
    (hreq : ∀ request ∈ alignmentCanonicalRequests n i,
      alignmentPivotRequestHolds q₀ b.val
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeScalePalette e heM F A S q₀ w x θ i) 1 request) :
    ∀ κ : Fin r, ∀ request ∈ alignmentCanonicalRequests n i,
      alignmentPivotRequestHolds q₀ b.val
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeInputPalette e heM F q₀ w x
          (fun T i => S T i (scaleBlockColorIndex B A hclosed b.val b.property
            (insert i T) (Finset.insert_nonempty _ _) κ) w) θ i) 1 request := by
  intro κ request hr
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hr
  have hh := hreq _ (List.mem_map.mpr ⟨T,hT,rfl⟩)
  change ∀ a ∈ ({1} : Finset ℚ), ∀ word ∈ alignmentTerminalWords
    (alignmentCanonicalTargetPairs n i T.val), _ at hh ⊢
  intro a ha word hw
  have ha1 : a = 1 := Finset.mem_singleton.mp ha
  subst a
  have h := congrFun (hh 1 (Finset.mem_singleton_self _) word hw) κ
  have hi : i ∉ T.val := fun hi => (lt_irrefl i)
    (alignmentCanonicalTargetTails_before T.val T.property i hi)
  have hmem := hclosed b.val b.property (insert i T.val) (Finset.insert_nonempty _ _)
  simpa only [one_mul, principalNativeScalePalette, principalNativeInputPalette,
    alignmentCanonicalRequest, alignmentTerminalRequest, Finset.erase_insert hi,
    dif_pos hmem, scaleBlockColorIndex] using h

end Hindman168
