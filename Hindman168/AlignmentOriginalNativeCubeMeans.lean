import Hindman168.AlignmentOriginalNativeCubeState

/-! Original empirical native cube means, with exact duplicated-component
product and face identities. The original box/residue grid and normalization
are unchanged, including algebraic zero means on empty grids. -/
namespace Hindman168
open FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentOriginalNativeCubeMean
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (d : ℕ)
    (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G)
    (obs : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ → ℂ) : ℂ :=
  complexExpectation (uniformFinsetMass
    (alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d))
    (fun ell => obs (alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell))

theorem alignment_original_native_cube_product_mean {χ : Type} [Fintype χ]
    (label : χ → ι) (slots : χ → AlignmentAddingPair N i → ℤ)
    (obs : ∀ z, (D (label z)).G ⧸ (D (label z)).Γ → ℂ)
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (d : ℕ)
    (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) :
    alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper
      shift weight g a (fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z) x))=
      alignmentOriginalProductCubeMean (fun z => D (label z)) F q₀ w T y p d ellResidue lower upper
        (fun z => shift (label z)) slots (fun z => weight (label z))
        (fun z => g (label z)) (fun z => a (label z)) obs := by
  unfold alignmentOriginalNativeCubeMean alignmentOriginalProductCubeMean
  congr 1
  funext ell
  apply Finset.prod_congr rfl
  intro z _
  rw [alignment_original_native_cube_state_reading]

theorem alignment_original_native_cube_translated_product_mean {χ : Type} [Fintype χ]
    (label : χ → ι) (slots : χ → AlignmentAddingPair N i → ℤ)
    (obs : ∀ z, (D (label z)).G ⧸ (D (label z)).Γ → ℂ)
    (action : ι → AlignmentAddingPair N i → ℤ)
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (d : ℕ)
    (ellResidue : Option κ → ℤ) (lower upper : Option κ → ℝ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) :
    alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a
      (fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z)
        (alignmentJointNativeCosetSlotTranslation D n v hv action x)))=
      alignmentOriginalProductCubeMean (fun z => D (label z)) F q₀ w T y p d ellResidue lower upper
        (fun z => shift (label z)) (fun z => slots z+action (label z)) (fun z => weight (label z))
        (fun z => g (label z)) (fun z => a (label z)) obs := by
  have he : (fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z)
      (alignmentJointNativeCosetSlotTranslation D n v hv action x)))=
      (fun x => ∏ z, obs z (alignmentJointNativeCosetEvaluation D n v hv (label z) (slots z+action (label z)) x)) := by
    funext x
    apply Finset.prod_congr rfl
    intro z _
    rw [alignment_joint_native_coset_slot_translation_evaluation]
  rw [he]
  exact alignment_original_native_cube_product_mean D n v hv label (fun z => slots z+action (label z))
    obs F q₀ w T y p Y d ellResidue lower upper shift weight g a

end Hindman168
