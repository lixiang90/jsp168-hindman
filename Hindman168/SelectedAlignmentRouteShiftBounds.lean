import Hindman168.SelectedAlignmentRouteNumericalWords
import Hindman168.SelectedAlignmentRoutePrelimitReadings
import Hindman168.MasterSamplingBudgets
import Hindman168.SamplingAsymptotics

/-! The finitely many actual route shifts have a fixed arithmetic budget.
The constants are chosen from the plan and incoming scales only, before the
width or raw sample. Original cutoff growth makes every shifted pivot in a
complete selected microcell positive. -/
namespace Hindman168
open Filter
open scoped Classical BigOperators Topology
attribute [local instance] alignmentAddingPairFintype

/-- The fallback residue is zero, so the size bound holds even for raw
samples outside the coprime support. -/
theorem selected_alignment_residue_representative_lt (q t L : ℕ) (hL : 0 < L) :
    alignmentResidueRepresentative q t L < L := by
  by_cases ht : Nat.Coprime t L
  · exact (alignmentResidueRepresentative_spec hL ht).1
  · simp only [alignmentResidueRepresentative, not_and_of_not_right _ ht, ↓reduceDIte]
    exact hL

theorem selected_alignment_pair_residue_lt_square
    {d M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A P F) (q₀ w : ℕ) {i : Fin M}
    (x : Fin M → ℕ) (a : AlignmentAddingPair M i) :
    alignmentPairResidue q₀ w (F.modulus w) a x < (F.modulus w : ℕ)^2 := by
  have hl := selected_alignment_residue_representative_lt
    (alignmentIntegerNumerator q₀ w a x) (alignmentNaturalBlockProduct x a.targetTail)
    ((F.modulus w:ℕ)*(primorial w)^w)
    (Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w)))
  exact hl.trans_le (by
    simpa only [pow_two] using Nat.mul_le_mul_left (F.modulus w:ℕ)
      (Nat.le_of_dvd (F.modulus w).pos (hF.primorial_power_dvd w)))

noncomputable def selectedAlignmentRouteShiftBudget {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) : ℕ :=
  1 + incoming.sup (fun b => (principalPivotRoutes plan).sup (fun route =>
    (alignmentIntegerSlotWeight (selectedAlignmentSlotExtension f
      (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)).natAbs))

theorem selected_alignment_route_shift_weight_le {n M : ℕ} {i : Fin n}
    (f : Fin n ↪o Fin M) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan) :
    alignmentIntegerSlotWeight (selectedAlignmentSlotExtension f
      (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd) ≤
      (selectedAlignmentRouteShiftBudget f q₀ plan incoming : ℤ) := by
  have hh := (Finset.le_sup (f := fun route =>
    (alignmentIntegerSlotWeight (selectedAlignmentSlotExtension f
      (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)).natAbs) hr).trans
    (Finset.le_sup (f := fun b => (principalPivotRoutes plan).sup (fun route =>
      (alignmentIntegerSlotWeight (selectedAlignmentSlotExtension f
        (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)).natAbs)) hb)
  exact Int.le_natAbs.trans (by exact_mod_cast (hh.trans (Nat.le_add_left _ _)))

theorem selected_alignment_route_shift_bound
    {d n M : ℕ} {i : Fin n} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (f : Fin n ↪o Fin M) (q₀ w : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan)
    (x : Fin M → ℕ) :
    |alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
      (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)| ≤
      (selectedAlignmentRouteShiftBudget f q₀ plan incoming : ℤ) * (F.modulus w : ℤ)^2 := by
  have hh := alignmentIntegerSlotShift_bound
    (fun a : AlignmentAddingPair M (f i) => alignmentPairResidue q₀ w (F.modulus w) a x)
    (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)
    ((F.modulus w:ℕ)^2) (fun a => (selected_alignment_pair_residue_lt_square hF q₀ w x a).le)
  refine hh.trans ?_
  simpa only [Nat.cast_pow, mul_comm] using mul_le_mul_of_nonneg_left
    (selected_alignment_route_shift_weight_le f q₀ plan incoming b hb route hr)
    (sq_nonneg (F.modulus w : ℤ))

theorem selected_alignment_route_shift_auxiliary_bound
    {d n M : ℕ} {i : Fin n} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (f : Fin n ↪o Fin M) (q₀ w : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) (b : Fin n → ℚ) (hb : b ∈ incoming)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ))) (hr : route ∈ principalPivotRoutes plan)
    (x : Fin M → ℕ) :
    |alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
      (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd)| ≤
      (selectedAlignmentRouteShiftBudget f q₀ plan incoming : ℤ) * (F.auxiliary w (f i).val : ℤ)^2 := by
  apply (selected_alignment_route_shift_bound hF f q₀ w plan incoming b hb route hr x).trans
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
  exact_mod_cast Nat.pow_le_pow_left (F.modulus_le_auxiliary w (f i).val) 2

/-- Coprimality is needed only in the nonzero branch of the canonical
residue. Thus its primorial divisibility also holds for arbitrary raw data. -/
theorem selected_alignment_pair_residue_divisible {M : ℕ} {i : Fin M}
    (F : MasterParameterFamily) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (x : Fin M → ℕ) (a : AlignmentAddingPair M i) :
    primorial w ∣ alignmentPairResidue q₀ w (F.modulus w) a x := by
  have hL : 0 < (F.modulus w:ℕ)*(primorial w)^w :=
    Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w))
  have hW : primorial w ∣ (primorial w)^w := by
    simpa only [pow_one] using pow_dvd_pow (primorial w) (by omega : 1 ≤ w)
  have hWL : primorial w ∣ (F.modulus w:ℕ)*(primorial w)^w := hW.trans (dvd_mul_left _ _)
  by_cases ht : Nat.Coprime (alignmentNaturalBlockProduct x a.targetTail)
      ((F.modulus w:ℕ)*(primorial w)^w)
  · have hs := alignmentResidueRepresentative_spec hL ht
      (q := alignmentIntegerNumerator q₀ w a x)
    apply alignment_residue_divisible (ht.of_dvd_right hWL) hWL
      (alignmentIntegerNumerator_divisible hq hw a x)
    simpa only [alignmentPairResidue, ← Nat.cast_mul, Int.natCast_modEq_iff] using hs.2
  · simp only [alignmentPairResidue, alignmentResidueRepresentative,
      not_and_of_not_right _ ht, ↓reduceDIte, dvd_zero]

theorem selected_alignment_route_shift_divisible
    {n M : ℕ} {i : Fin n} (F : MasterParameterFamily)
    (f : Fin n ↪o Fin M) {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (plan : List (AlignmentPivotStage n i)) (b : Fin n → ℚ)
    (route : List (ℕ × List (AlignmentAddingPair n i × ℚ)))
    (x : Fin M → ℕ) :
    (primorial w : ℤ) ∣
      alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd) :=
  alignmentIntegerSlotShift_divisible _ _ _
    (fun a => selected_alignment_pair_residue_divisible F hq hw x a)

theorem selected_alignment_route_shift_positive_eventually
    {d n M : ℕ} {i : Fin n} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (f : Fin n ↪o Fin M) (q₀ : ℕ) (plan : List (AlignmentPivotStage n i))
    (incoming : Finset (Fin n → ℚ)) :
    ∀ᶠ w in atTop, ∀ b ∈ incoming, ∀ route ∈ principalPivotRoutes plan,
      ∀ (x : Fin M → ℕ) (p : ℤ), (F.cutoff w (f i).val : ℤ) ≤ p →
      0 < p + alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (selectedAlignmentSlotExtension f (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd) := by
  let C := selectedAlignmentRouteShiftBudget f q₀ plan incoming
  have hh := (powerDominates_log_to_cutoff (hF.cutoff_auxiliary_growth (f i).val)).eventually_bound
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.cutoff w (f i).val)))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (F.auxiliary w (f i).val))) 2
    (show (0:ℝ) < C+1 by positivity)
  filter_upwards [hh] with w hw
  intro b hb route hr x p hp
  have hwz : ((C:ℤ)+1) * (F.auxiliary w (f i).val : ℤ)^2 ≤ F.cutoff w (f i).val := by
    exact_mod_cast hw
  have ha : (2:ℤ) ≤ F.auxiliary w (f i).val := by exact_mod_cast F.auxiliary_ge_two w (f i).val
  have hs := selected_alignment_route_shift_auxiliary_bound hF f q₀ w plan incoming b hb route hr x
  have hs' := (abs_le.mp hs).1
  change -((C:ℤ) * (F.auxiliary w (f i).val : ℤ)^2) ≤ _ at hs'
  nlinarith

/-- Every integer of a complete padding microcell has a positive shifted
pivot, simultaneously for all actual finite routes and all raw anchors. -/
theorem selected_alignment_complete_microcell_shift_positive
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (i : Fin n)
    (q₀ : ℕ) (plan : List (AlignmentPivotStage n i)) (incoming : Finset (Fin n → ℚ)) :
    ∀ᶠ w in atTop, ∀ b ∈ incoming, ∀ route ∈ principalPivotRoutes plan,
      ∀ x : Fin M → ℕ,
      (F.cutoff w (energyPrincipal e i) : ℤ) ≤
        ((x (principalAlignmentEmbedding e heM i) : ℤ) /
          (selectedPrincipalMicrocellWidth F e w i : ℤ)) *
          (selectedPrincipalMicrocellWidth F e w i : ℤ) →
      ∀ ell ∈ Finset.Ico 0 (selectedPrincipalMicrocellLength F e w i : ℤ),
      0 < alignmentMicrocellFirst (selectedPrincipalMicrocellWidth F e w i)
          (F.modulus w) (x (principalAlignmentEmbedding e heM i)) + (F.modulus w : ℤ)*ell +
        alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM)
            (alignmentJointRouteArithmetic q₀ plan b route).2.toAdd) := by
  filter_upwards [selected_alignment_route_shift_positive_eventually hF
    (principalAlignmentEmbedding e heM) q₀ plan incoming] with w hw
  intro b hb route hr x hleft ell hell
  apply hw b hb route hr x
  have hm : (0:ℤ) < (F.modulus w:ℕ) := by exact_mod_cast (F.modulus w).pos
  have hpoint := (alignment_residue_progression_interval
    (((x (principalAlignmentEmbedding e heM i):ℤ)/(selectedPrincipalMicrocellWidth F e w i:ℤ))*
      (selectedPrincipalMicrocellWidth F e w i:ℤ))
    (F.modulus w) (selectedPrincipalMicrocellLength F e w i)
    (x (principalAlignmentEmbedding e heM i)) ell hm).mpr (Finset.mem_Ico.mp hell)
  exact hleft.trans hpoint.1

end Hindman168
