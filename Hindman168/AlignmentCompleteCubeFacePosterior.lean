import Hindman168.AlignmentCompleteCubeFaceTransfer

/-! COMPLETE original finite-reading marginal cube test class all-face
failure vanishes under the ACTUAL posterior. Common coordinate/coefficient
budgets are DERIVED before sources/samples; no product-test-only conclusion. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem alignment_complete_cube_all_faces_posterior_vanishing
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ℝ) (L : NNReal)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G),
      event (conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x))
        (alignmentCompleteCubeAllFacesFailure (κ := κ) D F q₀ w T d shift slots g a B L c C ε) < δ := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  obtain ⟨B',L',R,hB',hR,hbudget⟩ := alignment_complete_cube_test_common_product_budget D B L (ε/4) (by positivity)
  have htolerance : 0 < ε/(2*R) := by positivity
  have hh := alignment_original_product_all_faces_posterior_vanishing (κ := κ) D n v hv r b
    hF q₀ hq T hT d hd c C K hc hC hK slots B' L' (fun ν => (hB' ν).le) htolerance hδ
  filter_upwards [hh,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro x hx htyp shift g a
  let μ := conditionMass (globalRawMass (F.cutoff w) (primorial w) N)
    (fun y => alignmentShortExposureKey F w i T y=alignmentShortExposureKey F w i T x)
  have hcap := hw x hx htyp shift g a
  apply lt_of_le_of_lt _ hcap
  apply event_mono μ (conditionMass_nonneg _ _ hraw.1)
  intro y hbad
  exact alignment_complete_cube_face_failure_subset_product D B L B' L' ε R hε hR hbudget
    F q₀ w T d shift slots g a c C y hbad

end Hindman168
