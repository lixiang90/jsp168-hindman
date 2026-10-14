import Hindman168.AlignmentJointOriginalProductCubeMean
import Hindman168.AlignmentOriginalDenominatorChoices
import Hindman168.AlignmentJointTerminalGridMeans

/-! Failure event for the LITERAL original nilsequence product cube law.
The denominator residue may depend on the sampled tuple/microcell, but its
original integer remainder is in the FULL fixed finite list chosen before w. -/
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

noncomputable def alignmentOriginalProductRemovalFailure
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (d : ℕ) (hd : 0 < d) (shift slots : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (B : ι → ℝ) (L : ι → NNReal) (c C ε : ℝ) (y : Fin N → ℕ) : Prop := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  exact ∃ (lower upper : Option κ → ℝ) (ellResidue : Option κ → ℤ)
      (obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)),
    (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
      c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
    (∀ ν, obs ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν)) ∧
    ε ≤ ‖alignmentOriginalProductCubeMean D F q₀ w T y p d ellResidue lower upper shift slots weight g a (fun ν => obs ν)-
      alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d
        (alignmentDenominatorChoice (alignmentDenominatorRemainder d hd
          (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z (ellResidue z))))
        shift weight g a (fun k : T => y k.val)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉)
        (alignmentJointNativeMetricProduct D n v hv slots obs)‖

end Hindman168
