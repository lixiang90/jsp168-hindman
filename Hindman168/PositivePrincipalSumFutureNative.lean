import Hindman168.PositivePrincipalSumFutureThreshold
import Hindman168.PositivePrincipalSumNativePalette

namespace Hindman168
open scoped BigOperators Classical

noncomputable def principalNativeInputObservation {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (F : MasterParameterFamily) (q₀ w : ℕ)
    (x : Fin M → ℕ) (S : Finset (Fin n) → Fin n → ℤ → ℝ) (i : Fin n) :
    Finset (Fin n) → ℚ → Multiplicative (AlignmentAddingPair M
      (principalAlignmentEmbedding e heM i) → ℤ) → Unit → ℝ :=
  fun B _ u _ => S (B.erase i) i
    (alignmentIntegerArrayArgument x (F.modulus w)
      (fun p => alignmentPairResidue q₀ w (F.modulus w) p x)
      (fun p => alignmentPairProgression q₀ w (F.modulus w) p x)
      ((B.erase i).image (principalAlignmentEmbedding e heM))
      (x (selectedPrincipalIndex e heM i)) u.toAdd u.toAdd)

theorem principal_adding_alignment_of_threshold_requests
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
      principalThresholdRequestHolds q₀ b
        (principalNativeLetter (principalAlignmentEmbedding e heM))
        (principalNativeInputObservation e heM F q₀ w x S i) θ 1 request) :
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
    have hc := principal_threshold_canonical_comparison q₀ b (principalNativeLetter f)
      (principalNativeInputObservation e heM F q₀ w x S i) θ 1 (hreq i) T htcanon
      selected List.filter_sublist ()
    have hi : i ∉ T := fun hi => (lt_irrefl i) (hbefore i hi)
    simp only [principalNativeInputObservation, Finset.erase_insert hi, smul_eq_mul,
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
    have hout := hc hcenter
    simpa only [finiteScaleBlockProduct, f, principalAlignmentEmbedding,
      OrderEmbedding.coe_ofStrictMono] using hout
  · have hempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    simp only [hempty, Finset.sum_empty, add_zero]
    linarith

end Hindman168
