import Hindman168.AlignmentCompleteCubeFaceFailure
import Hindman168.AlignmentCompleteCubeTestBudget
import Hindman168.AlignmentOriginalProductAllFacesPosterior
import Hindman168.AlignmentOriginalCubeProductLinearMean
import Hindman168.FiniteComplexCoefficientError

/-! Actual COMPLETE marginal face failure is contained in the ORIGINAL all
product-face failure using common fixed coordinate and coefficient budgets.
No endpoint, residue, normalization, source formula or vertex profile changes. -/
namespace Hindman168
open FiniteMass
open scoped BigOperators Classical
universe u
variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s)

theorem alignment_complete_cube_face_failure_subset_product
    (B : ℝ) (L : NNReal) (B' : ι → ℝ) (L' : ι → NNReal) (η R : ℝ) (hη : 0 < η) (hR : 0 < R) :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    (∀ obs ∈ boundedComplexLipschitzObservables (∀ ν, (D ν).G ⧸ (D ν).Γ) B L,
      ∃ l : List (ℂ × (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ))),
        (∀ t ∈ l, ∀ ν, t.2 ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B' ν) (L' ν)) ∧
        (l.map (fun t => ‖t.1‖)).sum < R ∧
        ‖obs-finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l‖ < η/4) →
    ∀ (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
      (shift slots : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) (c C : ℝ) (y : Fin N → ℕ),
      alignmentCompleteCubeAllFacesFailure (κ := κ) D F q₀ w T d shift slots g a B L c C η y →
      alignmentOriginalProductAllFacesFailure (β := κ) D F q₀ w T d shift slots g a B' L' c C (η/(2*R)) y := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro hbudget F q₀ w T d shift slots g a c C y hbad
  by_contra hnot
  obtain ⟨weight,hbits,e,he,j,lower,upper,ellResidue,obs,hbox,hobs,hlarge⟩ := hbad
  obtain ⟨l,hl,hsize,hclose⟩ := hbudget obs hobs
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let faceSlots := fun ν => slots ν+Pi.single e (weight ν j)
  have hlarge' := alignment_original_continuous_cube_face_approximation D F q₀ w T y p d ellResidue lower upper
    shift slots weight g a faceSlots obs (finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l)
    η hη hclose hlarge
  let original := fun t : ℂ × (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)) =>
    alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a (fun ν => t.2 ν)
  let translated := fun t : ℂ × (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)) =>
    alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a (fun ν => t.2 ν)
  have herror : ∀ t ∈ l, ‖translated t-original t‖ ≤ η/(2*R) := by
    intro t ht
    apply le_of_lt
    apply lt_of_not_ge
    intro h
    exact hnot ⟨weight,hbits,e,he,j,lower,upper,ellResidue,t.2,hbox,hl t ht,h⟩
  have hbound := finite_complex_list_positive_budget l (fun t => t.1) (fun t => translated t-original t)
    (η/(2*R)) R (by positivity) hsize herror
  have heq :
      alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift faceSlots weight g a
        (finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l)-
      alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a
        (finitePiProductLinearCombination (fun ν => (D ν).G ⧸ (D ν).Γ) l)=
      (l.map (fun t => t.1*(translated t-original t))).sum := by
    rw [alignment_original_continuous_cube_product_linear_mean,
      alignment_original_continuous_cube_product_linear_mean,finite_complex_list_linear_difference]
  rw [heq] at hlarge'
  have hc : R*(η/(2*R))=η/2 := by field_simp
  rw [hc] at hbound
  exact (not_lt_of_ge hlarge') hbound

end Hindman168
