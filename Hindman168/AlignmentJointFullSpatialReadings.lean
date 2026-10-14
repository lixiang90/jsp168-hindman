import Hindman168.AlignmentJointSourceRestriction
import Hindman168.AlignmentJointNativeSampleReadings

/-! Full joint spatial source matches ORIGINAL product observations at every
valid integer cube sample, including empty tails. The all-real tail congruence
is separate from the genuine integer nilsequence sample identity. -/
namespace Hindman168
open Module
open scoped Manifold ContDiff BigOperators
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

theorem alignment_joint_exposed_native_source_tail_congr
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N)) (x : Fin N → ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (weight : ι → κ → ℤ) (g a : ∀ ν, (D ν).G)
    (spatial : Option κ → ℝ) (t t' : Fin N → ℝ) (h : ∀ j ∈ T, t j=t' j) :
    alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a (Sum.elim spatial t)=
      alignmentJointExposedNativeSource D n v hv r b F q₀ w T x shift weight g a (Sum.elim spatial t') := by
  unfold alignmentJointExposedNativeSource nativeFinitePiVectorSource
  apply native_vector_polynomial_source_sample
  rw [native_vector_polynomial_source_log]
  exact alignment_joint_exposed_native_vector_tail_eval_congr D n v hv r b
    F q₀ w T x shift weight g a spatial t t' h


theorem alignment_joint_full_spatial_original_product_sample
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
    let z :=
      (fun j : Option κ => match j with
        | none => (alignmentCubeBase (F.modulus w) tau p Y ell : ℝ)
        | some j => ((tau*inc j : ℤ) : ℝ))
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentJointNativeMetricProduct D n v hv slot obs
        (alignmentJointTailSpatialSource D n v hv r b F q₀ w T x shift weight g a (fun k : T => y k.val) z : J.G ⧸ J.Γ) =
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
  have hc := alignment_joint_exposed_native_source_tail_congr D n v hv r b F q₀ w T x
    shift weight g a
    (fun j : Option κ => match j with
      | none => (alignmentCubeBase (F.modulus w) (alignmentNaturalBlockProduct y T) p
          ((alignmentShortBinStart F w i T x : ℤ)/(F.modulus w : ℤ)) ell : ℝ)
      | some j => (((alignmentNaturalBlockProduct y T : ℤ)*inc j : ℤ) : ℝ))
    (fun k => (alignmentTailTuple T x (fun k : T => y k.val) k : ℝ)) (fun k => (y k : ℝ))
    (by
      intro k hk
      exact congrArg (fun n : ℕ => (n : ℝ))
        (alignment_tail_tuple_inside T x (fun k : T => y k.val) (⟨k,hk⟩ : T)))
  unfold alignmentJointTailSpatialSource
  rw [hc]
  exact alignment_joint_native_metric_product_actual_sample D n v hv r b
    hF hq hw T hT hx hy hkey p ell hp inc weight shift slot g a obs

end Hindman168
