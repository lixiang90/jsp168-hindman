import Hindman168.AlignmentJointMetricProducts
import Hindman168.AlignmentJointRemovedNativeSource

/-! The native metric product test equals the ORIGINAL simultaneous
component observations at genuine cube samples. This closes the value-level
link between the actual joint source and its uniformly approximated tests. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u

section ProductValues
variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_joint_native_metric_product_apply (z : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ (F : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)) (y : J.G ⧸ J.Γ),
      alignmentJointNativeMetricProduct D n v hv z F y =
        ∏ ν, F ν (alignmentJointNativeCosetEvaluation D n v hv ν (z ν) y) := by
  dsimp only
  intro F y
  simp only [alignmentJointNativeMetricProduct,id_eq,ContinuousMap.prod_apply,
    alignment_joint_native_metric_reading_apply]
end ProductValues

section ActualSamples
variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_joint_native_metric_product_actual_sample
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    {q₀ w : ℕ} (hq : 0 < q₀) (hw : q₀+1 ≤ w)
    (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i) {x y : Fin N → ℕ}
    (hx : ∀ j, Nat.Coprime (x j) (primorial w))
    (hy : ∀ j, Nat.Coprime (y j) (primorial w))
    (hkey : alignmentShortExposureKey F w i T x=alignmentShortExposureKey F w i T y)
    (p ell : ℤ) (hp : Int.ModEq (F.modulus w : ℕ) p (y i))
    (inc : κ → ℤ) (weight : ι → κ → ℤ) (shift slot : ι → AlignmentAddingPair N i → ℤ)
    (g a : ∀ ν, (D ν).G) :
    let Y : ℤ := (alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)
    let tau : ℤ := alignmentNaturalBlockProduct y T
    let z := Sum.elim
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ)) (fun j : Fin N => (y j : ℝ))
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentJointNativeMetricProduct D n v hv slot obs
        (alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a z : J.G ⧸ J.Γ) =
      ∏ ν, obs ν ((g ν ^ (alignmentIntegerArrayArgument y (F.modulus w)
        (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
        (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T
        (p+(F.modulus w : ℤ)*(ell+∑ j, weight ν j*inc j)) (shift ν) (slot ν)/(F.modulus w : ℤ)) * a ν :
        (D ν).G ⧸ (D ν).Γ)) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs
  have he := alignment_joint_exposed_native_source_actual_sample D n v hv r b hF hq hw T hT
    hx hy hkey p ell hp inc weight shift g a
  have hobs := congrArg (fun h : J.G => alignmentJointNativeMetricProduct D n v hv slot obs
    (h : J.G ⧸ J.Γ)) he
  apply hobs.trans
  rw [alignment_joint_native_metric_product_apply]
  apply Finset.prod_congr rfl
  intro ν _
  change obs ν (((alignmentNativeCanonicalCubeArray (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w)
      (fun e => alignmentPairResidue q₀ w (F.modulus w) e y)
      (fun e => alignmentPairProgression q₀ w (F.modulus w) e y) T p
      ((alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)) ell inc (weight ν) (shift ν)).val (slot ν) :
        (D ν).G ⧸ (D ν).Γ)) = _
  exact congrArg (fun h : (D ν).G => obs ν (h : (D ν).G ⧸ (D ν).Γ))
    (alignmentNativeCanonicalCubeArray_evaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G)
      (n ν) (v ν) (hv ν) (g ν) (a ν) y (F.modulus w) (F.modulus w).pos
      _ _ T p _ ell inc (weight ν) (shift ν) (slot ν))
end ActualSamples

end Hindman168
