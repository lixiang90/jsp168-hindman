import Hindman168.AlignmentJointActualRemovalChain

/-! Failure of the COMPLETE joint mean removal on literal ORIGINAL permitted
cube boxes. This retains original numerical observer classes and all original
endpoints; no narrowed event or separately supplied analytic cap is inserted. -/
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

noncomputable def alignmentJointOriginalBoxRemovalFailure
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (d : ℕ) (Y rho : ℤ) (residueChoice : Option κ → ℤ)
    (shift slots : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (B : ι → ℝ) (L : ι → NNReal) (c C ε : ℝ) (y : Fin N → ℕ) : Prop := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  exact ∃ (lower upper : Option κ → ℝ) (obs : C(J.G ⧸ J.Γ,ℂ)),
    (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
      c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
    obs ∈ alignmentJointOriginalTestFamily D n v hv slots B L ∧
    ε ≤ ‖alignmentJointTailResidueMean D n v hv r b F q₀ w T T x d Y rho residueChoice shift weight g a
        (fun k : T => y k.val)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉) obs-
      alignmentJointTailResidueMean D n v hv r b F q₀ w T ∅ x d Y rho residueChoice shift weight g a
        (fun k : T => y k.val)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉)
        (fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉) obs‖

end Hindman168
