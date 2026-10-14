import Hindman168.SelectedAlignmentSourceExposure
import Hindman168.PositivePrincipalSumNativeReadings

/-! The original ambient joint orbit reads the actual selected integer
arguments. Frozen recipes retain the prediction padding gap and the original
ambient modulus and master scales. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology BigOperators Classical
universe u

/-- Exact transport of the same original joint source, not a marginal model. -/
theorem selected_alignment_joint_reading_integer_argument
    {ι : Type} [Fintype ι] {n M s : ℕ} (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin n))
    (x : Fin n → ℕ) (p : ℤ) (shift : ι → AlignmentAddingPair n i → ℤ)
    (g a : ∀ ν, (D ν).G) (ell : ℤ) (ν : ι)
    (slots : AlignmentAddingPair n i → ℤ) (obs : (D ν).G ⧸ (D ν).Γ → ℝ) :
    obs (alignmentJointNativeCosetEvaluation D r v hv ν
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots)
      (QuotientGroup.mk (alignmentOriginalJointPointOrbit D r v hv F q₀ w
        (fun k => (T k).image (principalAlignmentEmbedding e heM))
        (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) p
        (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift k)) g a ell))) =
      obs ((g ν ^ (alignmentIntegerArrayArgument x (F.modulus w)
          (fun a => selectedAlignmentPairResidue M e q₀ w (F.modulus w) a x)
          (fun a => selectedAlignmentPairProgression M e q₀ w (F.modulus w) a x)
          (T ν) (p + (F.modulus w : ℤ)*ell) (shift ν) slots / (F.modulus w : ℤ)) *
        a ν : (D ν).G ⧸ (D ν).Γ)) := by
  have hh := principal_native_joint_reading_integer_argument D r v hv F q₀ w
    (fun k => (T k).image (principalAlignmentEmbedding e heM))
    (selectedAlignmentSampleExtension (principalAlignmentEmbedding e heM) x) p
    (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift k))
    g a ell ν (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots) obs
  rw [selected_alignment_canonical_array_argument] at hh
  exact hh

/-- The residue component uses only the genuine exposed congruences. It
therefore works for the gap view without assigning that view master conditions. -/
theorem selected_alignment_exposure_canonical_residue
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ w : ℕ) (T : Finset (Fin n))
    (hT : ∀ k ∈ T, k < i) {x y : Fin M → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w)) (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) x =
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) y)
    (stored query : AlignmentAddingPair n i → ℤ) (p : ℤ)
    (hp : Int.ModEq (F.modulus w : ℕ) p (y (principalAlignmentEmbedding e heM i))) :
    alignmentIntegerArrayArgument y (F.modulus w)
      (fun a => alignmentPairResidue q₀ w (F.modulus w) a y)
      (fun a => alignmentPairProgression q₀ w (F.modulus w) a y)
      (T.image (principalAlignmentEmbedding e heM)) p
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
      (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query) % (F.modulus w : ℤ) =
    alignmentPivotArrayResidue x (T.image (principalAlignmentEmbedding e heM)) (F.modulus w)
      (x (principalAlignmentEmbedding e heM i))
      (alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)) := by
  rw [alignmentIntegerArrayArgument_residue]
  have hexp := alignmentShortExposureKey_rawExposure _ w _ _ hkey
  have hs := alignmentRawExposure_slot_shift_eq hF q₀ w hx hy hexp
    (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
  have ht := alignmentRawExposure_tail_modEq hexp (by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact (principalAlignmentEmbedding e heM).strictMono (hT k hk)) (dvd_mul_right (F.modulus w:ℕ) _)
  have hxy : Int.ModEq (F.modulus w:ℕ) (x (principalAlignmentEmbedding e heM i))
      (y (principalAlignmentEmbedding e heM i)) :=
    Int.natCast_modEq_iff.mpr (alignmentShortExposureKey_pivot_residue
      (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w _ _ hkey)
  unfold alignmentPivotArrayResidue
  rw [← hs]
  exact ht.symm.mul ((hp.trans hxy.symm).add_right _)

/-- Both coordinates of the actual padding piece are frozen on the fiber. -/
theorem selected_alignment_exposure_canonical_piece
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (q₀ : ℕ) (hq : 0 < q₀) (C : ℕ)
    (V U : Finset (AlignmentAddingPair n i → ℤ)) :
    ∀ᶠ w in atTop, ∀ T : Finset (Fin n), (∀ k ∈ T, k < i) → ∀ x y : Fin M → ℕ,
      (∀ k, k < i → x (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      (∀ k ∈ T, 0 < x (principalAlignmentEmbedding e heM k)) →
      (∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2) →
      (∀ j, Nat.Coprime (x j) (primorial w)) → (∀ j, Nat.Coprime (y j) (primorial w)) →
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) x =
      alignmentShortExposureKey
        (alignmentGeometryWithGap F (energyPrincipal e i) (energyPadding e i)) w
        (principalAlignmentEmbedding e heM i) (T.image (principalAlignmentEmbedding e heM)) y →
      intervalInteriorRoot (F.gap w (energyPadding e i))
        ((C+3) * F.auxiliary w (energyPadding e i) * selectedPrincipalMicrocellWidth F e w i)
        ((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i) : ℕ) : ℤ) →
      ∀ stored ∈ V, ∀ query ∈ U, ∀ p : ℤ,
      Int.ModEq (F.modulus w:ℕ) p (y (principalAlignmentEmbedding e heM i)) →
      |p - y (principalAlignmentEmbedding e heM i)| ≤ (C * selectedPrincipalMicrocellWidth F e w i : ℕ) →
      intervalResiduePiece (F.gap w (energyPadding e i)) (F.modulus w)
        (alignmentIntegerArrayArgument y (F.modulus w)
          (fun a => alignmentPairResidue q₀ w (F.modulus w) a y)
          (fun a => alignmentPairProgression q₀ w (F.modulus w) a y)
          (T.image (principalAlignmentEmbedding e heM)) p
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored)
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) query)) =
      (((alignmentNaturalBlockProduct x (T.image (principalAlignmentEmbedding e heM)) *
          x (principalAlignmentEmbedding e heM i) : ℕ) : ℤ) / (F.gap w (energyPadding e i):ℤ),
        alignmentPivotArrayResidue x (T.image (principalAlignmentEmbedding e heM)) (F.modulus w)
          (x (principalAlignmentEmbedding e heM i))
          (alignmentIntegerSlotShift (fun a => alignmentPairResidue q₀ w (F.modulus w) a x)
            (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) stored))) := by
  filter_upwards [selected_alignment_exposure_interval_stable hF e heM i q₀ hq C V U] with w hw
  intro T hT x y hx hpos hy hxc hyc hkey hinterior stored hstored query hquery p hp hdist
  exact Prod.ext (hw T hT x y hx hpos hy hyc hkey hinterior stored hstored query hquery p hdist)
    (selected_alignment_exposure_canonical_residue hF e heM i q₀ w T hT hxc hyc hkey stored query p hp)

end Hindman168
