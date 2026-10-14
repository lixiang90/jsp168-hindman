import Hindman168.SelectedAlignmentSourceKeyRecipes

/-! The key recipe has exactly the existing source interface:
gKey w key nu. Each actual source component supplies its own target's
exposed key, while the functions themselves are fixed before extraction. -/
namespace Hindman168
open FiniteMass
open scoped Classical Manifold ContDiff
universe u

noncomputable def selectedAlignmentFamilyKeyRecipe {ι : Type*} {α : ι → Type*} {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ C : ℕ) (T : ι → Finset (Fin n))
    (V U : ι → Finset (AlignmentAddingPair n i → ℤ)) (stored : ι → AlignmentAddingPair n i → ℤ)
    (recipe : ∀ ν, ℕ → (ℤ × ℤ) → α ν) : ℕ → SelectedAlignmentShortKey M → ∀ ν, α ν :=
  fun w key ν => selectedAlignmentKeyRecipe F e heM i q₀ C (T ν) (V ν) (U ν) (stored ν) (recipe ν) w key

theorem selected_alignment_family_key_recipe_eq {ι : Type*} {α : ι → Type*} {n M : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (q₀ w C : ℕ) (T : ι → Finset (Fin n))
    (V U : ι → Finset (AlignmentAddingPair n i → ℤ)) (hzero : ∀ ν, 0 ∈ U ν)
    (stored : ι → AlignmentAddingPair n i → ℤ) (hstored : ∀ ν, stored ν ∈ V ν)
    (recipe : ∀ ν, ℕ → (ℤ × ℤ) → α ν)
    (x : Fin M → ℕ) (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hx : ∀ ν, selectedAlignmentFullExposureArrayStable F e heM i q₀ w C (T ν) (V ν) (U ν) x) :
    (fun ν => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U stored recipe w
      (selectedAlignmentSourceKey F e heM i w (T ν) x) ν) =
    (fun ν => recipe ν w (selectedAlignmentFullFrozenLabel F e heM i q₀ w (T ν) x (stored ν))) := by
  funext ν
  exact selected_alignment_key_recipe_eq F e heM i q₀ w C (T ν) (V ν) (U ν) (hzero ν)
    x hxs (hx ν) (stored ν) (hstored ν) (recipe ν)

/-- Actual frozen reading with exactly the preselected per-key g/a source
interface, rather than recipes selected after the raw anchor. -/
theorem selected_alignment_key_recipe_native_joint_reading
    {ι : Type} [Fintype ι] {n M s : ℕ} (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M)
    (i : Fin n) (D : ι → NativeNilmanifoldData.{u} s) (r : ι → ℕ)
    (v : ∀ ν, Fin (r ν+1) → AlignmentAddingPair M (principalAlignmentEmbedding e heM i) → ℤ)
    (hv : ∀ ν, Function.Injective (alignmentNativeFiniteEvaluation
      (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (r ν) (v ν)))
    (F : MasterParameterFamily) (q₀ w C : ℕ)
    (T : ι → Finset (Fin n)) (ν : ι) (V U : ι → Finset (AlignmentAddingPair n i → ℤ))
    (hzero : ∀ k, 0 ∈ U k) (x y : Fin M → ℕ)
    (hxs : x ∈ (globalRawMass (F.cutoff w) (primorial w) M).support)
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hcut : ∀ k, k < i → y (principalAlignmentEmbedding e heM k) ≤ F.cutoff w (energyPrincipal e k)^2)
    (hkey : selectedAlignmentSourceKey F e heM i w (T ν) x = selectedAlignmentSourceKey F e heM i w (T ν) y)
    (hgood : ∀ k, selectedAlignmentFullExposureArrayStable F e heM i q₀ w C (T k) (V k) (U k) x)
    (shift : ι → AlignmentAddingPair n i → ℤ) (hshift : ∀ k, shift k ∈ V k)
    (slots : AlignmentAddingPair n i → ℤ) (hslots : slots ∈ U ν)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w:ℕ) p (y (principalAlignmentEmbedding e heM i)))
    (hdist : |p + (F.modulus w:ℤ)*ell-y (principalAlignmentEmbedding e heM i)| ≤
      (C*selectedPrincipalMicrocellWidth F e w i:ℕ))
    (obs : ∀ k, ℕ → (ℤ × ℤ) → C((D k).G ⧸ (D k).Γ, ℝ))
    (g a : ∀ k, ℕ → (ℤ × ℤ) → (D k).G) :
    let key := fun k => selectedAlignmentSourceKey F e heM i w (T k) x
    piecewiseLinearNilsequence (D ν).Γ F (fun _ => (⟨energyPadding e i, heM _⟩ : Fin M))
      (obs ν) (g ν) (a ν) w
      (alignmentIntegerArrayArgument y (F.modulus w)
        (fun b => alignmentPairResidue q₀ w (F.modulus w) b y)
        (fun b => alignmentPairProgression q₀ w (F.modulus w) b y)
        ((T ν).image (principalAlignmentEmbedding e heM)) (p+(F.modulus w:ℤ)*ell)
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift ν))
        (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots)) =
      selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U shift obs w (key ν) ν
        (alignmentJointNativeCosetEvaluation D r v hv ν
          (selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) slots)
          (QuotientGroup.mk (alignmentOriginalJointPointOrbit D r v hv F q₀ w
            (fun k => (T k).image (principalAlignmentEmbedding e heM)) y p
            (fun k => selectedAlignmentSlotExtension (principalAlignmentEmbedding e heM) (shift k))
            (fun k => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U shift g w (key k) k)
            (fun k => selectedAlignmentFamilyKeyRecipe F e heM i q₀ C T V U shift a w (key k) k) ell))) := by
  dsimp only
  rw [selected_alignment_family_key_recipe_eq F e heM i q₀ w C T V U hzero shift hshift g x hxs hgood,
    selected_alignment_family_key_recipe_eq F e heM i q₀ w C T V U hzero shift hshift a x hxs hgood]
  have ho := congrFun (selected_alignment_family_key_recipe_eq F e heM i q₀ w C T V U hzero
    shift hshift obs x hxs hgood) ν
  rw [ho]
  exact selected_alignment_full_native_joint_frozen_piece_reading e heM i D r v hv F q₀ w C T ν
    (V ν) (U ν) x y hy hcut hkey (hgood ν) shift (hshift ν) slots hslots p ell hp hdist obs g a

end Hindman168
