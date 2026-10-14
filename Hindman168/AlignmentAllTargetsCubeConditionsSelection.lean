import Hindman168.AlignmentAllTargetsNativeCountableSelection
import Hindman168.AlignmentAllCubeConditionsSelection

/-! One actual supported sample sequence satisfies every numerical cube
condition for every target family. The target, source parameters, and exposure
are fixed independently of the numerical-condition index. This is a selection
statement, not a claim identifying separately chosen local Haar witnesses. -/
set_option maxHeartbeats 2000000

namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : ℕ → Type} [∀ t, Fintype (ι t)]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ∀ t, ι t → NativeNilmanifoldData.{u} s) (n : ∀ t, ι t → ℕ)
  (v : ∀ t ν, Fin (n t ν + 1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ t ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D t ν).E) (I := (D t ν).I)
      (G := (D t ν).G) (n t ν) (v t ν)))
  (r : ∀ t, ι t → ℕ)
  (b : ∀ t ν, Basis (Fin (r t ν)) ℝ
    (alignmentNativeArrayData (D t ν) (n t ν) (v t ν) (hv t ν)).E)

include n v hv r b in
theorem alignment_all_targets_all_cube_conditions_supported_selection_of_enumeration
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : ℕ → Finset (Fin N))
    (hT : ∀ t j, j ∈ T t → j < i)
    (cond : ℕ → ℕ × AlignmentCubeConditionIndex) (hcond : Function.Surjective cond)
    (shift : ∀ t w : ℕ,
      ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι t → AlignmentAddingPair N i → ℤ)
    (g a : ∀ t w : ℕ,
      ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ∀ ν, (D t ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop,
      β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j)) :
    ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ j in atTop,
        sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧
        S j (sample j)) ∧
      ∀ t (idx : AlignmentCubeConditionIndex), ∀ᶠ j in atTop,
        ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin idx.1)
          (D t) (n t) (v t) (hv t) F q₀ (W j) (T t) (idx.2.1 + 1)
          (shift t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          (g t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          (a t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          idx.2.2.2.2.1 idx.2.2.2.2.2.1
          (1 / (idx.2.2.2.1 + 1 : ℝ)) idx.2.2.1
          (1 / (idx.2.2.2.2.2.2 + 1 : ℝ)) (sample j) := by
  obtain ⟨stage, sample, hstage, hstagele, hs, hgood⟩ :=
    alignment_all_targets_native_cube_countable_supported_selection
      (ι := fun q => ι (cond q).1) (κ := fun q => Fin (cond q).2.1)
      (fun q => D (cond q).1) (fun q => n (cond q).1)
      (fun q => v (cond q).1) (fun q => hv (cond q).1)
      (fun q => r (cond q).1) (fun q => b (cond q).1)
      hF q₀ hq (fun q => T (cond q).1) (fun q => hT (cond q).1)
      (fun q => (cond q).2.2.1 + 1) (fun _ => Nat.zero_lt_succ _)
      (fun q => 1 / ((cond q).2.2.2.2.1 + 1 : ℝ))
      (fun q => ((cond q).2.2.2.1 : ℝ))
      (fun q => (cond q).2.2.2.1 + 1)
      (fun _ => one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))
      (fun _ => Nat.cast_nonneg _)
      (fun _ => by simp only [Nat.cast_add, Nat.cast_one]; exact le_rfl)
      (fun q => ((cond q).2.2.2.2.2.1 : ℝ))
      (fun q => ((cond q).2.2.2.2.2.2.1 : NNReal))
      (fun q => 1 / ((cond q).2.2.2.2.2.2.2 + 1 : ℝ))
      (fun _ => one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))
      (fun q => shift (cond q).1) (fun q => g (cond q).1) (fun q => a (cond q).1)
      W hW S hβ hS (fun _ _ => True)
      (fun _ => Filter.Eventually.of_forall (fun _ => trivial))
  refine ⟨sample, hs.mono (fun _ h => ⟨h.1, h.2.1⟩), ?_⟩
  have lift (P : ℕ → AlignmentCubeConditionIndex → Prop)
      (hh : ∀ q, P (cond q).1 (cond q).2) : ∀ t idx, P t idx := by
    intro t idx
    obtain ⟨q, heq⟩ := hcond (t, idx)
    simpa only [heq] using hh q
  exact lift _ hgood


include n v hv r b in
theorem alignment_all_targets_all_cube_conditions_supported_selection
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : ℕ → Finset (Fin N))
    (hT : ∀ t j, j ∈ T t → j < i)
    (shift : ∀ t w : ℕ,
      ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι t → AlignmentAddingPair N i → ℤ)
    (g a : ∀ t w : ℕ,
      ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ∀ ν, (D t ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop,
      β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j)) :
    ∃ sample : ℕ → Fin N → ℕ,
      (∀ᶠ j in atTop,
        sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧
        S j (sample j)) ∧
      ∀ t (idx : AlignmentCubeConditionIndex), ∀ᶠ j in atTop,
        ¬ alignmentNativeCompleteCubeAllFacesFailure (κ := Fin idx.1)
          (D t) (n t) (v t) (hv t) F q₀ (W j) (T t) (idx.2.1 + 1)
          (shift t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          (g t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          (a t (W j) (alignmentShortExposureKey F (W j) i (T t) (sample j)))
          idx.2.2.2.2.1 idx.2.2.2.2.2.1
          (1 / (idx.2.2.2.1 + 1 : ℝ)) idx.2.2.1
          (1 / (idx.2.2.2.2.2.2 + 1 : ℝ)) (sample j) := by
  exact alignment_all_targets_all_cube_conditions_supported_selection_of_enumeration D n v hv r b hF q₀ hq T hT
    (Denumerable.ofNat (ℕ × AlignmentCubeConditionIndex))
    (fun idx => ⟨Encodable.encode idx, Denumerable.ofNat_encode idx⟩)
    shift g a W hW S hβ hS

end Hindman168
