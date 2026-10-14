import Hindman168.AlignmentNativeCompleteCubeCountableSelection
import Mathlib.Logic.Denumerable

/-! Explicit enumeration BEFORE selection of every dimension, positive modulus,
integer geometry/test budget and reciprocal accuracy. The source choices do
not change with the condition index. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

abbrev AlignmentCubeConditionIndex := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

variable {ι : Type} [Fintype ι] 
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_native_all_cube_conditions_supported_selection_of_enumeration
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (cond : ℕ → AlignmentCubeConditionIndex) (hcond : Function.Surjective cond)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
    : ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ j in atTop, sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧ S j (sample j)) ∧
      ∀ idx : AlignmentCubeConditionIndex, ∀ᶠ j in atTop,
        ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin idx.1) D n v hv F q₀ (W j) T (idx.2.1+1)
          (shift (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          (g (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          (a (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          idx.2.2.2.2.1 idx.2.2.2.2.2.1 (1/(idx.2.2.2.1+1 : ℝ)) idx.2.2.1
          (1/(idx.2.2.2.2.2.2+1 : ℝ)) (sample j) := by
  obtain ⟨stage,sample,hstage,hstagele,hs,hgood⟩ :=
    alignment_native_complete_cube_countable_supported_selection (κ := fun q => Fin (cond q).1)
      D n v hv r b hF q₀ hq T hT
      (fun q => (cond q).2.1+1) (fun _ => Nat.zero_lt_succ _)
      (fun q => 1/((cond q).2.2.2.1+1 : ℝ)) (fun q => ((cond q).2.2.1 : ℝ))
      (fun q => (cond q).2.2.1+1) (fun _ => one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one)) (fun _ => Nat.cast_nonneg _)
      (fun _ => by simp only [Nat.cast_add,Nat.cast_one]; exact le_rfl)
      (fun q => ((cond q).2.2.2.2.1 : ℝ)) (fun q => ((cond q).2.2.2.2.2.1 : NNReal))
      (fun q => 1/((cond q).2.2.2.2.2.2+1 : ℝ)) (fun _ => one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))
      (fun _ => shift) (fun _ => g) (fun _ => a) W hW S hβ hS
      (fun _ _ => True) (fun _ => Filter.Eventually.of_forall (fun _ => trivial))
  refine ⟨sample,hs.mono (fun _ h => ⟨h.1,h.2.1⟩),?_⟩
  intro idx
  obtain ⟨q,rfl⟩ := hcond idx
  exact hgood q

include n v hv r b in
theorem alignment_native_all_cube_conditions_supported_selection
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (shift : ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
    : ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ j in atTop, sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧ S j (sample j)) ∧
      ∀ idx : AlignmentCubeConditionIndex, ∀ᶠ j in atTop,
        ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin idx.1) D n v hv F q₀ (W j) T (idx.2.1+1)
          (shift (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          (g (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          (a (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
          idx.2.2.2.2.1 idx.2.2.2.2.2.1 (1/(idx.2.2.2.1+1 : ℝ)) idx.2.2.1
          (1/(idx.2.2.2.2.2.2+1 : ℝ)) (sample j) := by
  exact alignment_native_all_cube_conditions_supported_selection_of_enumeration D n v hv r b
    hF q₀ hq T hT (Denumerable.ofNat AlignmentCubeConditionIndex)
    (fun idx => ⟨Encodable.encode idx,Denumerable.ofNat_encode idx⟩)
    shift g a W hW S hβ hS

end Hindman168
