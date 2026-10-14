import Hindman168.AlignmentOriginalProductRemovalFailure

/-! Failure of the LITERAL original marginal product cube law under the
original own-pair upper-face slot action. All original boxes, residues and
bounded/Lipschitz observer choices remain quantified AFTER the sampled tuple.
No terminal law or source surrogate occurs in this event. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Classical
universe u

noncomputable def alignmentOriginalProductFaceFailure
    {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ] {N : ℕ} {i : Fin N} {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily) (q₀ w : ℕ)
    (T : Finset (Fin N)) (d : ℕ) (shift slots : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (B : ι → ℝ) (L : ι → NNReal) (c C ε : ℝ)
    (e : AlignmentAddingPair N i) (j : κ) (y : Fin N → ℕ) : Prop := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  exact ∃ (lower upper : Option κ → ℝ) (ellResidue : Option κ → ℤ)
      (obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)),
    (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
      c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
    (∀ ν, obs ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν)) ∧
    ε ≤ ‖alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift
        (fun ν => slots ν+Pi.single e (weight ν j)) weight g a (fun ν => obs ν)-
      alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift
        slots weight g a (fun ν => obs ν)‖

end Hindman168
