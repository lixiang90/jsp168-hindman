import Hindman168.AlignmentOriginalContinuousCubeMean
import Hindman168.BoundedComplexLipschitzObservables

/-! LITERAL complete marginal cube test failure under ALL original own faces
and zero/one vertex profiles. Complete tests, original boxes/residues and the
failing original face remain selectable AFTER the actual posterior sample. -/
namespace Hindman168
open scoped BigOperators Classical
universe u
noncomputable def alignmentCompleteCubeAllFacesFailure
    {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (q₀ w : ℕ)
    (T : Finset (Fin N)) (d : ℕ) (shift slots : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) (B : ℝ) (L : NNReal) (c C η : ℝ) (y : Fin N → ℕ) : Prop := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  exact ∃ weight : ι → κ → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) ∧
    ∃ e : AlignmentAddingPair N i, e.targetTail=T ∧ ∃ (j : κ) (lower upper : Option κ → ℝ)
      (ellResidue : Option κ → ℤ) (obs : C((∀ ν, (D ν).G ⧸ (D ν).Γ),ℂ)),
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
      obs ∈ boundedComplexLipschitzObservables (∀ ν, (D ν).G ⧸ (D ν).Γ) B L ∧
      η ≤ ‖alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift
          (fun ν => slots ν+Pi.single e (weight ν j)) weight g a obs-
        alignmentOriginalContinuousCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a obs‖
end Hindman168
