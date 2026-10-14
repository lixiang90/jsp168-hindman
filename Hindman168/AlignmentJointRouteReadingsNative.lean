import Hindman168.AlignmentJointRouteReadingsCover
import Hindman168.AlignmentJointNativeSlotTranslations
import Hindman168.NativeFinitePiCosetRestriction

/-! The readings used by the fixed closed options are the actual frozen
component observables on the full joint quotient. A finite factor lookup
returns zero outside its stored catalogue. The single-letter reading identity
is derived from the genuine restricted-coset lift and slot evaluation. -/
namespace Hindman168
open scoped Topology Manifold ContDiff
universe u

variable {ι κ : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

/-- R_(B,a,c;stored,query), defined on the whole original joint quotient.
The lookup and limiting observables are fixed independently of all subsequent
coset representatives and shear lifts. -/
noncomputable def alignmentJointRouteNativeReading
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (B : Finset (Fin N)) (a : ℚ) (c : κ)
    (stored query : AlignmentAddingPair N i → ℤ)
    (y : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) : ℝ :=
  match factor B a c stored with
  | none => 0
  | some ν => obs ν (alignmentJointNativeCosetEvaluation D n v hv ν query y)

/-- An actual stored factor has exactly its original native reading. -/
theorem alignment_joint_route_native_reading_some
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (B : Finset (Fin N)) (a : ℚ) (c : κ)
    (stored query : AlignmentAddingPair N i → ℤ) (ν : ι)
    (hfactor : factor B a c stored = some ν) (y) :
    alignmentJointRouteNativeReading D n v hv factor obs B a c stored query y =
      obs ν (alignmentJointNativeCosetEvaluation D n v hv ν query y) := by
  simp only [alignmentJointRouteNativeReading, hfactor]

theorem alignment_joint_route_native_reading_continuous
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (hobs : ∀ ν, Continuous (obs ν))
    (B : Finset (Fin N)) (a : ℚ) (c : κ)
    (stored query : AlignmentAddingPair N i → ℤ) :
    Continuous (alignmentJointRouteNativeReading D n v hv factor obs B a c stored query) := by
  unfold alignmentJointRouteNativeReading
  cases factor B a c stored with
  | none => exact continuous_const
  | some ν => exact (hobs ν).comp (alignment_joint_native_coset_evaluation_continuous D n v hv ν query)

/-- Original supplied metrics and their actual topology are retained. -/
theorem alignment_joint_route_native_reading_metric_continuous
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
      fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (∀ ν, Continuous (obs ν)) →
    ∀ B a c stored query,
      Continuous (alignmentJointRouteNativeReading D n v hv factor obs B a c stored query) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
    fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro hobs B a c stored query
  unfold alignmentJointRouteNativeReading
  cases factor B a c stored with
  | none => exact continuous_const
  | some ν => exact (hobs ν).comp (alignment_joint_native_metric_coset_evaluation_continuous D n v hv ν query)

theorem alignment_joint_native_evaluation_restriction
    {η : Type} [Fintype η] (index : η → ι) (k : η)
    (query : AlignmentAddingPair N i → ℤ) (y) :
    alignmentJointNativeCosetEvaluation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) k query
      (nativeFinitePiCosetRestriction
        (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index y) =
      alignmentJointNativeCosetEvaluation D n v hv (index k) query y := by
  unfold alignmentJointNativeCosetEvaluation
  dsimp only [Function.comp_apply]
  exact congrArg (alignmentArrayNativeCosetEvaluation (D (index k)) (n (index k))
    (v (index k)) (hv (index k)) query)
    (native_finite_pi_coset_restriction_coordinate
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index y k)

/-- Apply a genuine marginal lift equality to the stored component, then use
the proved slot-translation evaluation identity. This derives the raw
single-letter identity required by the ordered-word theorem. -/
theorem alignment_joint_route_native_reading_restricted_lift
    {η : Type} [Fintype η] (index : η → ι) (k : η)
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ)
    (B : Finset (Fin N)) (a : ℚ) (c : κ)
    (stored query delta : AlignmentAddingPair N i → ℤ)
    (hfactor : factor B a c stored = some (index k))
    (y y' : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (hlift : nativeFinitePiCosetRestriction
        (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index y' =
      alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k)) (fun _ => delta)
        (nativeFinitePiCosetRestriction
          (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) index y)) :
    alignmentJointRouteNativeReading D n v hv factor obs B a c stored query y' =
      alignmentJointRouteNativeReading D n v hv factor obs B a c stored (query+delta) y := by
  simp only [alignmentJointRouteNativeReading, hfactor]
  apply congrArg (obs (index k))
  rw [← alignment_joint_native_evaluation_restriction D n v hv index k query y', hlift,
    alignment_joint_native_coset_slot_translation_evaluation,
    alignment_joint_native_evaluation_restriction]

end Hindman168
