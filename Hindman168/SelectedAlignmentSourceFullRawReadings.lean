import Hindman168.SelectedAlignmentSourceFullRawStable

/-! Actual prediction recipes read at the same original joint orbit on
all the good exposure fibers established with probability tending to one. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

/-- There is one common joint source, one frozen label per stored factor,
and the recipe is the original padding-gap recipe. -/
theorem selected_alignment_full_native_joint_frozen_piece_reading
    {ι : Type} [Fintype ι] {n M s : ℕ} (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (F : MasterParameterFamily) (q₀ w C : ℕ)
    (T : ι → Finset (Fin n)) (ν : ι) (V U : Finset (AlignmentAddingPair n i → ℤ))
    (x y : Fin M → ℕ)
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hcut : ∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2)
    (hkey : alignmentShortExposureKey
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
      (principalAlignmentEmbedding e heM i) ((T ν).image (principalAlignmentEmbedding e heM))
      x =
      alignmentShortExposureKey
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
      (principalAlignmentEmbedding e heM i) ((T ν).image (principalAlignmentEmbedding e heM)) y)
    (hgood : selectedAlignmentFullExposureArrayStable F e heM i q₀ w C (T ν) V U x)
    (shift : ι → AlignmentAddingPair n i → ℤ) (hshift : shift ν ∈ V)
    (slots : AlignmentAddingPair n i → ℤ) (hslots : slots ∈ U)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w:ℕ) p (y (principalAlignmentEmbedding e heM i)))
    (hdist : |p + (F.modulus w:ℤ)*ell-y (principalAlignmentEmbedding e heM i)| ≤
      (C*selectedPrincipalMicrocellWidth F e w i:ℕ))
    (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
    (g a : ∀ ν, ℕ → (ℤ × ℤ) → (D ν).G) :
    let label := fun k => selectedAlignmentFullFrozenLabel F e heM i q₀ w (T k) x (shift k)
    piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i, heM _⟩ : Fin M))
      (obs ν) (g ν) (a ν) w
      (alignmentIntegerArrayArgument y (F.modulus w)
        (fun b => alignmentPairResidue q₀ w (F.modulus w) b y)
        (fun b => alignmentPairProgression q₀ w (F.modulus w) b y)
        ((T ν).image (principalAlignmentEmbedding e heM)) (p+(F.modulus w:ℤ)*ell)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift ν))
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots)) =
      obs ν w (label ν) (alignmentJointNativeCosetEvaluation D r v hv ν
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots)
        (QuotientGroup.mk (alignmentOriginalJointPointOrbit D r v hv F q₀ w
          (fun k => (T k).image (principalAlignmentEmbedding e heM)) y p
          (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift k))
          (fun k => g k w (label k)) (fun k => a k w (label k)) ell))) := by
  let label := fun k => selectedAlignmentFullFrozenLabel F e heM i q₀ w (T k) x (shift k)
  have hp' : Int.ModEq (F.modulus w:ℕ) (p+(F.modulus w:ℤ)*ell)
      (y (principalAlignmentEmbedding e heM i)) := by
    change (p+(F.modulus w:ℤ)*ell) % (F.modulus w:ℤ) =
      (y (principalAlignmentEmbedding e heM i):ℤ) % (F.modulus w:ℤ)
    change p % (F.modulus w:ℤ) = (y (principalAlignmentEmbedding e heM i):ℤ) % (F.modulus w:ℤ) at hp
    simpa only [Int.add_emod, Int.mul_emod, Int.emod_self, zero_mul, Int.zero_emod,
      add_zero, Int.emod_emod] using hp
  have hpiece := hgood y hy hcut hkey (shift ν) hshift slots hslots
    (p+(F.modulus w:ℤ)*ell) hp' hdist
  have hr := principal_native_joint_reading_integer_argument D r v hv F q₀ w
    (fun k => (T k).image (principalAlignmentEmbedding e heM)) y p
    (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift k))
    (fun k => g k w (label k)) (fun k => a k w (label k)) ell ν
    (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots) (obs ν w (label ν))
  dsimp only
  unfold piecewiseLinearNilsequence
  rw [hpiece]
  exact hr.symm

/-- Mapped canonical arithmetic depends only on the selected coordinates,
even when all unused ambient coordinates keep their actual sampled values. -/
theorem selected_alignment_full_native_integer_numerator {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin M → ℕ) :
    alignmentIntegerNumerator q₀ w (p.map (principalAlignmentEmbedding e heM)) x =
      selectedAlignmentIntegerNumerator M e q₀ w p (fun k => x (principalAlignmentEmbedding e heM k)) := by
  unfold alignmentIntegerNumerator selectedAlignmentIntegerNumerator
  rw [AlignmentAddingPair.map_sourceBlock, AlignmentAddingPair.map_targetBlock,
    principal_alignment_native_scale, principal_alignment_native_scale, alignment_natural_block_product_image]

theorem selected_alignment_full_native_pair_residue {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin M → ℕ) :
    alignmentPairResidue q₀ w modulus (p.map (principalAlignmentEmbedding e heM)) x =
      selectedAlignmentPairResidue M e q₀ w modulus p (fun k => x (principalAlignmentEmbedding e heM k)) := by
  unfold alignmentPairResidue selectedAlignmentPairResidue
  rw [selected_alignment_full_native_integer_numerator]
  change alignmentResidueRepresentative _
    (alignmentNaturalBlockProduct _ (p.targetTail.image (principalAlignmentEmbedding e heM))) _ = _
  rw [alignment_natural_block_product_image]

theorem selected_alignment_full_native_pair_progression {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (p : AlignmentAddingPair n i) (x : Fin M → ℕ) :
    alignmentPairProgression q₀ w modulus (p.map (principalAlignmentEmbedding e heM)) x =
      selectedAlignmentPairProgression M e q₀ w modulus p (fun k => x (principalAlignmentEmbedding e heM k)) := by
  unfold alignmentPairProgression selectedAlignmentPairProgression
  rw [selected_alignment_full_native_integer_numerator, selected_alignment_full_native_pair_residue]
  change alignmentProgressionShift _
    (alignmentNaturalBlockProduct _ (p.targetTail.image (principalAlignmentEmbedding e heM))) _ _ = _
  rw [alignment_natural_block_product_image]

theorem selected_alignment_full_canonical_array_argument {n M : ℕ}
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) (q₀ w modulus : ℕ) {i : Fin n}
    (x : Fin M → ℕ) (T : Finset (Fin n)) (p : ℤ)
    (stored query : AlignmentAddingPair n i → ℤ) :
    alignmentIntegerArrayArgument x modulus (fun a => alignmentPairResidue q₀ w modulus a x)
      (fun a => alignmentPairProgression q₀ w modulus a x) (T.image (principalAlignmentEmbedding e heM)) p
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query) =
    alignmentIntegerArrayArgument (fun k => x (principalAlignmentEmbedding e heM k)) modulus
      (fun a => selectedAlignmentPairResidue M e q₀ w modulus a (fun k => x (principalAlignmentEmbedding e heM k)))
      (fun a => selectedAlignmentPairProgression M e q₀ w modulus a (fun k => x (principalAlignmentEmbedding e heM k)))
      T p stored query := by
  unfold alignmentIntegerArrayArgument
  rw [alignment_natural_block_product_image, selected_alignment_slot_shift,
    selected_alignment_array_progression]
  simp only [selected_alignment_full_native_pair_residue, selected_alignment_full_native_pair_progression]
  rfl

/-- Thus the full-raw frozen factor has exactly the selected stored label;
only the exposure anchor retains the other genuine raw coordinates. -/
theorem selected_alignment_full_frozen_label_restriction {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w : ℕ) (T : Finset (Fin n)) (x : Fin M → ℕ)
    (stored : AlignmentAddingPair n i → ℤ) :
    selectedAlignmentFullFrozenLabel F e heM i q₀ w T x stored =
      selectedAlignmentFrozenLabel F e heM i q₀ w T
        (fun k => x (principalAlignmentEmbedding e heM k)) stored := by
  simp only [selectedAlignmentFullFrozenLabel, selectedAlignmentFrozenLabel, alignmentPivotArrayResidue,
    alignment_natural_block_product_image, selected_alignment_sample_extension_apply,
    selected_alignment_slot_shift,
    selected_alignment_full_native_pair_residue]

end Hindman168
