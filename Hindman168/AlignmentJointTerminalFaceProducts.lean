import Hindman168.AlignmentJointTerminalFaceMean
import Hindman168.AlignmentJointTranslatedTestFamilies
import Hindman168.AlignmentJointActualTerminalTranslation

/-! The ACTUAL terminal d law has uniformly vanishing original marginal
product face discrepancy. This uses the literal own-pair slot automorphism,
supported actual tuples, exposed key and real original numerical geometry.
It does not yet compare both original cube laws to this terminal law. -/
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

theorem alignment_joint_terminal_product_face_mean
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (d : ℕ) (choice lo hi : Option κ → ℤ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ)
    (g a : ∀ ν, (D ν).G) (j : κ) (e : AlignmentAddingPair N i) (he : e.targetTail=T)
    (slots : ι → AlignmentAddingPair N i → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentJointTranslatedDenominatorMean D n v hv r b F q₀ w T x d choice shift weight g a
        (fun k : T => y k.val) lo hi
        (fun k => if k=some j then alignmentPairProgression q₀ w (F.modulus w) e y else 0)
        (alignmentJointNativeMetricProduct D n v hv slots obs)=
      alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a
        (fun k : T => y k.val) lo hi
        (alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+Pi.single e (weight ν j)) obs) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs
  rw [alignment_joint_terminal_denominator_face_mean D n v hv r b hF hq hw T hT hx hy hkey
    d choice lo hi shift weight g a j e he (alignmentJointNativeMetricProduct D n v hv slots obs)]
  congr 1
  funext z
  exact congrArg (fun f : C(J.G ⧸ J.Γ,ℂ) => f z)
    (alignment_joint_native_translated_metric_product_eq D n v hv slots
      (fun ν => Pi.single e (weight ν j)) obs)

theorem alignment_joint_actual_terminal_product_face_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) (d : ℕ) (hd : 0 < d)
    (c C : ℝ) (Kbox : ℕ) (hc : 0 < c) (hC : 0 ≤ C) (hKbox : C+1 ≤ (Kbox : ℝ))
    (slots : ι → AlignmentAddingPair N i → ℤ) (B : ι → ℝ) (L : ι → NNReal) (hB : ∀ ν, 0 ≤ B ν)
    {ε : ℝ} (hε : 0 < ε) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ᶠ w in atTop, ∀ x y : Fin N → ℕ,
      x ∈ (globalRawMass (F.cutoff w) (primorial w) N).support →
      alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y →
      y ∈ (globalRawMass (F.cutoff w) (primorial w) N).support →
      ∀ lower upper : Option κ → ℝ,
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) →
      ∀ (e : AlignmentAddingPair N i) (_he : e.targetTail=T) (coordinate : κ) (choice : Option κ → ℤ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G),
      let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
      let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
      let lo := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈lower z⌉
      let hi := fun z => alignmentCubeCoordinate (F.modulus w) (alignmentNaturalBlockProduct y T) p Y z ⌈upper z⌉
      ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      (∀ ν, obs ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν)) →
      ‖alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi
          (alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+Pi.single e (weight ν coordinate)) obs)-
        alignmentJointDenominatorSpatialMean D n v hv r b F q₀ w T x d choice shift weight g a
          (fun k : T => y k.val) lo hi (alignmentJointNativeMetricProduct D n v hv slots obs)‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have hh := alignment_joint_actual_terminal_translation_eventually (κ := κ) D n v hv r b
    hF q₀ hq T d hd c C Kbox hc hC hKbox slots B L hB hε
  filter_upwards [hh,eventually_ge_atTop (q₀+1)] with w hw hwq
  intro x y hx hkey hy lower upper hbox e he coordinate choice shift weight g a obs hobs
  have hbound := hw x y hy lower upper hbox e (some coordinate) choice shift weight g a
    (alignmentJointNativeMetricProduct D n v hv slots obs) ⟨obs,(fun ν _ => hobs ν),rfl⟩
  rw [alignment_joint_terminal_product_face_mean D n v hv r b hF hq hwq T hT
    (alignmentGlobalRawMass_support_coprime F w x hx) (alignmentGlobalRawMass_support_coprime F w y hy)
    hkey d choice _ _ shift weight g a coordinate e he slots obs] at hbound
  exact hbound

end Hindman168
