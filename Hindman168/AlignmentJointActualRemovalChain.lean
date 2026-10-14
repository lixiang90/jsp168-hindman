import Hindman168.AlignmentJointActualRemovalStep
import Hindman168.OrderedRemovalTelescope

/-! Complete factor-removal chain for the SAME joint spatial source and
SAME original permitted cube endpoints. On the original good events its
full-tail versus denominator-only mean error is at most |T| times eta. -/
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

theorem alignment_joint_actual_removal_chain_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (η : ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      ∀ y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support,
      alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y →
      ∀ lower upper : Option κ → ℝ,
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) →
      ∀ (q₀ : ℕ) (rho : ℤ) (residueChoice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
      let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
      let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
      (∀ j : T, ¬alignmentJointTailRemovalEvent D n v hv r b F q₀ w T (orderedRetainedTail T j.val) x j d Y rho residueChoice
        shift slots weight g a B L (c/2) (alignmentOriginalResidualUpper T.card K C) η (fun k : T => y k.val)) →
      ∀ obs : C(J.G ⧸ J.Γ,ℂ), obs ∈ alignmentJointOriginalTestFamily D n v hv slots B L →
      ‖alignmentJointTailResidueMean D n v hv r b F q₀ w T T x d Y rho residueChoice
        shift weight g a (fun k : T => y k.val) lo hi obs-
        alignmentJointTailResidueMean D n v hv r b F q₀ w T ∅ x d Y rho residueChoice
        shift weight g a (fun k : T => y k.val) lo hi obs‖ ≤ (T.card : ℝ)*η := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  filter_upwards [alignment_joint_actual_removal_step_eventually (κ := κ) D n v hv r b hF T hT d hd c C K hc hC hK slots B L η]
    with w hw
  intro x hx y hy hkey lower upper hbox q₀ rho residueChoice shift weight g a hgood obs hobs
  let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
  let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
  let f : Finset (Fin N) → ℂ := fun U => alignmentJointTailResidueMean D n v hv r b F q₀ w T U x d Y rho
    residueChoice shift weight g a (fun k : T => y k.val) lo hi obs
  change ‖f T-f ∅‖ ≤ (T.card : ℝ)*η
  have hstep (j : Fin N) (hj : j ∈ T) :
      ‖f (insert j (orderedRetainedTail T j))-f (orderedRetainedTail T j)‖ ≤ η := by
    have hh := hw x hx y hy hkey lower upper hbox (orderedRetainedTail T j) (ordered_retained_tail_subset T j)
      (⟨j,hj⟩ : T) (ordered_retained_tail_excludes T j) q₀ rho residueChoice shift weight g a
      (hgood ⟨j,hj⟩) obs hobs
    exact hh.le
  exact ordered_removal_telescope_le (α := Fin N) T f η hstep

end Hindman168
