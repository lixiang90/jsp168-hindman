import Hindman168.AlignmentCompleteCubeFacePositiveSelection
import Hindman168.CountablePositiveEventDiagonal

/-! Actual raw-law selection on any cofinal width subsequence inside prescribed
positive events, simultaneously for a countable list of original complete cube
conditions. Every condition retains uniformity over all its endpoints/tests.
The modulus list is fixed before any later local-law period is chosen. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {κ : ℕ → Type} [∀ q, Fintype (κ q)]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_complete_cube_countable_supported_selection
    {k : ℕ} {A : Finset ℚ} {P₀ : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P₀ F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ → ℕ) (hd : ∀ q, 0 < d q) (c C : ℕ → ℝ) (K : ℕ → ℕ)
    (hc : ∀ q, 0 < c q) (hC : ∀ q, 0 ≤ C q) (hK : ∀ q, C q+1 ≤ (K q : ℝ))
    (slots : ℕ → ι → AlignmentAddingPair N i → ℤ) (B : ℕ → ℝ) (L : ℕ → NNReal)
    (η : ℕ → ℝ) (hη : ∀ q, 0 < η q)
    (shift : ℕ → ℕ → ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
      ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ _q _w : ℕ,
      ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G)
    (W : ℕ → ℕ) (hW : Tendsto W atTop atTop)
    (S : ℕ → (Fin N → ℕ) → Prop) {β : ℝ} (hβ : 0 < β)
    (hS : ∀ᶠ j in atTop, β ≤ event (globalRawMass (F.cutoff (W j)) (primorial (W j)) N) (S j))
    (Extra : ℕ → ℕ → Prop) (hExtra : ∀ q, ∀ᶠ j in atTop, Extra q j) :
    ∃ (stage : ℕ → ℕ) (sample : ℕ → Fin N → ℕ), Tendsto stage atTop atTop ∧
      (∀ j, stage j ≤ j) ∧
      (∀ᶠ j in atTop,
        sample j ∈ (globalRawMass (F.cutoff (W j)) (primorial (W j)) N).support ∧
        S j (sample j) ∧ Extra (stage j) j) ∧
      ∀ q, ∀ᶠ j in atTop, ¬ alignmentCompleteCubeAllFacesFailure (κ := κ q)
        D F q₀ (W j) T (d q)
        (shift q (W j) (alignmentShortExposureKey F (W j) i T (sample j))) (slots q)
        (g q (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
        (a q (W j) (alignmentShortExposureKey F (W j) i T (sample j)))
        (B q) (L q) (c q) (C q) (η q) (sample j) := by
  let μ j := globalRawMass (F.cutoff (W j)) (primorial (W j)) N
  let Bad q j y := alignmentCompleteCubeAllFacesFailure (κ := κ q) D F q₀ (W j) T (d q)
    (shift q (W j) (alignmentShortExposureKey F (W j) i T y)) (slots q)
    (g q (W j) (alignmentShortExposureKey F (W j) i T y))
    (a q (W j) (alignmentShortExposureKey F (W j) i T y)) (B q) (L q) (c q) (C q) (η q) y
  have hμ : ∀ᶠ j in atTop, ∀ y, 0 ≤ μ j y :=
    hW.eventually ((alignmentGlobalRawMass_geometry hF).mono (fun _ h => h.1))
  have hBad q : Tendsto (fun j => event (μ j) (Bad q j)) atTop (𝓝 0) :=
    (alignment_complete_cube_all_faces_global_tendsto (κ := κ q) D n v hv r b
      hF q₀ hq T hT (d q) (hd q) (c q) (C q) (K q) (hc q) (hC q) (hK q)
      (slots q) (B q) (L q) (shift q) (g q) (a q) (hη q)).comp hW
  exact countable_positive_event_diagonal μ Bad hμ hBad S hβ hS Extra hExtra

end Hindman168
