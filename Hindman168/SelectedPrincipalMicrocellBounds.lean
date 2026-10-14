import Hindman168.AlignmentExposedArrayOffsets
import Hindman168.SelectedPrincipalMicrocellGrowth
import Hindman168.PositivePrincipalSumNativeIndices
import Hindman168.AlignmentNumericalPolynomialBounds

namespace Hindman168
open scoped BigOperators Classical

theorem selected_principal_earlier_product_bound
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (w : ℕ) (i : Fin n) (x : Fin n → ℕ)
    (hx : ∀ k, k < i → x k ≤ F.cutoff w (energyPrincipal e k)^2)
    (T : Finset (Fin n)) (hT : ∀ k ∈ T, k < i) :
    principalSubsetProduct T x ≤ selectedPrincipalAuxiliary F e w i := by
  have hs : T ⊆ Finset.univ.filter (fun k : Fin n => k < i) := by
    intro k hk; simp [hT k hk]
  calc
    _ ≤ ∏ k ∈ T, F.cutoff w (energyPrincipal e k)^2 :=
      Finset.prod_le_prod' (fun k hk => hx k (hT k hk))
    _ ≤ ∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i), F.cutoff w (energyPrincipal e k)^2 :=
      Finset.prod_le_prod_of_subset_of_one_le' hs
        (fun k _ _ => one_le_pow₀ (hF.cutoff_positive w _))
    _ ≤ _ := by unfold selectedPrincipalAuxiliary; omega

/-- Only selected earlier coordinates are bounded. Unselected raw values
may be arbitrary; no large full-principal auxiliary budget is introduced. -/
theorem selected_principal_native_numerator_bound
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (q₀ w : ℕ) {i : Fin n} (p : AlignmentAddingPair n i)
    (x : Fin M → ℕ)
    (hx : ∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) :
    alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x ≤
      selectedPrincipalAuxiliary F e w i ^ 2 := by
  have hp := selected_principal_earlier_product_bound hF e w i
    (fun k => x (principalAlignmentEmbedding e heM k)) hx _ (alignmentPair_source_before p)
  have hm : (F.modulus w : ℕ) ≤ selectedPrincipalAuxiliary F e w i := by
    unfold selectedPrincipalAuxiliary; omega
  unfold alignmentIntegerNumerator
  rw [AlignmentAddingPair.map_sourceBlock, AlignmentAddingPair.map_targetBlock,
    principal_alignment_native_scale, principal_alignment_native_scale,
    alignment_natural_block_product_image]
  have hd := (Nat.div_le_self (selectedSubsetScale M e w (alignmentPairSourceBlock p))
    (q₀ * selectedSubsetScale M e w (alignmentPairTargetBlock p))).trans
      (hF.selected_subset_scale_bound e heM w (alignmentPairSourceBlock p)).2
  calc
    _ ≤ (F.modulus w : ℕ) * selectedPrincipalAuxiliary F e w i := Nat.mul_le_mul hd hp
    _ ≤ _ := by simpa only [pow_two] using Nat.mul_le_mul_right (selectedPrincipalAuxiliary F e w i) hm

theorem selected_principal_native_progression_bound
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (q₀ w : ℕ) {i : Fin n} (p : AlignmentAddingPair n i)
    (x : Fin M → ℕ)
    (hx : ∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2)
    (ρ : ℕ) (hρ : ρ ≤ (F.modulus w : ℕ)^2) (Δ : ℤ)
    (hexact : (F.modulus w : ℤ) * Δ =
      (alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x : ℤ) -
      (alignmentNaturalBlockProduct x (p.targetTail.image (principalAlignmentEmbedding e heM)) : ℤ) * ρ) :
    |(F.modulus w : ℤ) * Δ| ≤ 2 * (selectedPrincipalAuxiliary F e w i : ℤ)^3 := by
  have hq : (alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x : ℤ) ≤
      (selectedPrincipalAuxiliary F e w i : ℤ)^2 := by
    exact_mod_cast selected_principal_native_numerator_bound hF e heM q₀ w p x hx
  have ht : (alignmentNaturalBlockProduct x (p.targetTail.image (principalAlignmentEmbedding e heM)) : ℤ) ≤
      selectedPrincipalAuxiliary F e w i := by
    rw [alignment_natural_block_product_image]
    exact_mod_cast selected_principal_earlier_product_bound hF e w i
      (fun k => x (principalAlignmentEmbedding e heM k)) hx _ (alignmentPair_target_before p)
  have hm : (F.modulus w : ℕ) ≤ selectedPrincipalAuxiliary F e w i := by
    unfold selectedPrincipalAuxiliary; omega
  have hr : (ρ : ℤ) ≤ (selectedPrincipalAuxiliary F e w i : ℤ)^2 := by
    exact_mod_cast hρ.trans (Nat.pow_le_pow_left hm 2)
  have ha : (2 : ℤ) ≤ selectedPrincipalAuxiliary F e w i := by
    exact_mod_cast (show 2 ≤ selectedPrincipalAuxiliary F e w i by unfold selectedPrincipalAuxiliary; omega)
  have hprod := mul_le_mul ht hr (Int.natCast_nonneg ρ) (Int.natCast_nonneg _)
  rw [hexact, abs_le]
  constructor <;> nlinarith [sq_nonneg (selectedPrincipalAuxiliary F e w i : ℤ),
    Int.natCast_nonneg (alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x),
    mul_nonneg (Int.natCast_nonneg (alignmentNaturalBlockProduct x (p.targetTail.image (principalAlignmentEmbedding e heM))))
      (Int.natCast_nonneg ρ)]

/-- The actual original residue/progression satisfies the selected budget;
its exact division equation is supplied by the existing arithmetic theorem. -/
theorem selected_principal_actual_progression_bound
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    {i : Fin n} (p : AlignmentAddingPair n i) (x : Fin M → ℕ)
    (hunit : ∀ j, Nat.Coprime (x j) (primorial w))
    (hx : ∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) :
    |(F.modulus w : ℤ) * alignmentPairProgression q₀ w (F.modulus w)
      (p.map (principalAlignmentEmbedding e heM)) x| ≤
      2 * (selectedPrincipalAuxiliary F e w i : ℤ)^3 := by
  have hr := alignmentPairResidue_master_data hF hq hw x hunit
    (p.map (principalAlignmentEmbedding e heM))
  apply selected_principal_native_progression_bound hF e heM q₀ w p x hx _ hr.2.1.le
  exact alignmentPairProgression_exact hF hq hw x hunit _

theorem selected_principal_actual_slot_shift_bound
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    {i : Fin n} (x : Fin M → ℕ) (hunit : ∀ j, Nat.Coprime (x j) (primorial w))
    (v : AlignmentAddingPair n i → ℤ) :
    let rho := fun p : AlignmentAddingPair n i => alignmentPairResidue q₀ w (F.modulus w)
      (p.map (principalAlignmentEmbedding e heM)) x
    (primorial w : ℤ) ∣ alignmentIntegerSlotShift rho v ∧
      |alignmentIntegerSlotShift rho v| ≤ ((F.modulus w : ℕ)^2 : ℕ) * alignmentIntegerSlotWeight v := by
  dsimp only
  have hr (p : AlignmentAddingPair n i) := alignmentPairResidue_master_data hF hq hw x hunit
    (p.map (principalAlignmentEmbedding e heM))
  exact ⟨alignmentIntegerSlotShift_divisible _ v _ (fun p => (hr p).2.2.1),
    alignmentIntegerSlotShift_bound _ v _ (fun p => (hr p).2.1.le)⟩
end Hindman168
