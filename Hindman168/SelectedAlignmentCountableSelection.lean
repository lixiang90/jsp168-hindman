import Hindman168.SelectedAlignmentFaceLimit
import Hindman168.CountablePositiveEventDiagonal

/-! Actual raw-law selection on any cofinal width subsequence inside prescribed
positive events, simultaneously for countably many HETEROGENEOUS original target/model families and actual native complete cube
conditions. The target, model index type, native groups, determining evaluations, basis, cube dimension and numerical data may vary with each fixed condition. Every condition retains all endpoint/test quantifiers.
The modulus list is fixed before any later local-law period is chosen. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : ℕ → Type} [∀ q, Fintype (ι q)]
  {κ : ℕ → Type} [∀ q, Fintype (κ q)]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ∀ q, ι q → NativeNilmanifoldData.{u} s) (n : ∀ q, ι q → ℕ)
  (v : ∀ q ν, Fin (n q ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ q ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D q ν).E) (I := (D q ν).I) (G := (D q ν).G) (n q ν) (v q ν)))
  (r : ∀ q, ι q → ℕ) (b : ∀ q ν, Basis (Fin (r q ν)) ℝ
    (alignmentNativeArrayData (D q ν) (n q ν) (v q ν) (hv q ν)).E)

include n v hv r b in
theorem selected_alignment_all_targets_native_cube_countable_supported_selection
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : ℕ → Finset (Fin N)) (hT : ∀ q j, j ∈ T q → j < gap)
    (d : ℕ → ℕ) (hd : ∀ q, 0 < d q) (c C : ℕ → ℝ) (K : ℕ → ℕ)
    (hc : ∀ q, 0 < c q) (hC : ∀ q, 0 ≤ C q) (hK : ∀ q, C q+1 ≤ (K q : ℝ))
    (B : ℕ → ℝ) (L : ℕ → NNReal)
    (η : ℕ → ℝ) (hη : ∀ q, 0 < η q)
    (shift : ∀ _q _w : ℕ, ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι _q → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _q _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D _q ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
    (Extra : ℕ → ℕ → Prop) (hExtra : ∀ q, ∀ᶠ j in atTop, Extra q j) :
    ∃ (stage : ℕ → ℕ) (sample : ℕ → Fin N → ℕ), Tendsto stage atTop atTop ∧
      (∀ j, stage j ≤ j) ∧
      (∀ᶠ j in atTop,
        sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧
        S j (sample j) ∧ Extra (stage j) j) ∧
      ∀ q, ∀ᶠ j in atTop, ¬ selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ q)
        (D q) (n q) (v q) (hv q) (alignmentGeometryWithGap F i gap) gap q₀ (W j) (T q) (d q)
        (shift q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) (sample j)))
        (g q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) (sample j)))
        (a q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) (sample j)))
        (B q) (L q) (c q) (C q) (η q) (sample j) := by
  let μ j := globalRawMass (F.cutoff (W j)) (primorial (W j)) N
  let Bad q j y := selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ q) (D q) (n q) (v q) (hv q) (alignmentGeometryWithGap F i gap) gap q₀ (W j) (T q) (d q)
    (shift q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) y))
    (g q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) y))
    (a q (W j) (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) (W j) i (T q) y)) (B q) (L q) (c q) (C q) (η q) y
  have hμ : ∀ᶠ j in atTop, ∀ y, 0 ≤ μ j y :=
    hW.eventually ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1))
  have hBad q : Tendsto (fun j => event (μ j) (Bad q j)) atTop (𝓝 0) :=
    (selected_alignment_native_complete_cube_all_faces_global_tendsto (κ := κ q) (D q) (n q) (v q) (hv q) (r q) (b q)
      hF gap hgap q₀ hq (T q) (hT q) (d q) (hd q) (c q) (C q) (K q) (hc q) (hC q) (hK q)
      (B q) (L q) (shift q) (g q) (a q) (hη q)).comp hW
  exact countable_positive_event_diagonal μ Bad hμ hBad S hβ hS Extra hExtra

end Hindman168
