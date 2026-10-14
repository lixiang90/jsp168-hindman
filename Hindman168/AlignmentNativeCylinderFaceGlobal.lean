import Hindman168.AlignmentNativeCylinderOriginalFailure
import Hindman168.AlignmentOriginalProductAllFacesGlobal

/-! Actual ORIGINAL raw-law cylinder failure vanishes uniformly before every
exposed-key-selected source. The cylinder presentation derives all numerical
budgets; the old analytic cap is instantiated on the actual duplicated family. -/
namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
omit [DecidableEq ι] in
theorem alignment_native_cylinder_all_faces_global_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ (l : List C(J.G ⧸ J.Γ,ℂ)),
      (∀ f ∈ l, f ∈ alignmentJointNativeCylinderGenerators D n v hv) →
      ∀ᶠ w in atTop, ∀ (shift : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
          ι → AlignmentAddingPair N i → ℤ)
        (g a : ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G),
        event (globalRawMass (F.cutoff w) (primorial w) N)
          (fun y => alignmentNativeCylinderCubeAllFacesFailure (κ := κ) D n v hv F q₀ w T d
            (shift (alignmentShortExposureKey F w i T y))
            (g (alignmentShortExposureKey F w i T y)) (a (alignmentShortExposureKey F w i T y)) c C τ l.prod y) < δ := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro l hl
  obtain ⟨label,slots,obs,B,L,hB,hpresentation⟩ := alignment_native_cylinder_list_original_presentation D n v hv l hl
  have hh := alignment_original_product_all_faces_global_eventually (κ := κ)
    (fun z => D (label z)) (fun z => n (label z)) (fun z => v (label z)) (fun z => hv (label z))
    (fun z => r (label z)) (fun z => b (label z))
    hF q₀ hq T hT d hd c C K hc hC hK slots B L (fun z => (hB z).1.le) hτ hδ
  filter_upwards [hh,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro shift g a
  have hcap := hw (fun key z => shift key (label z)) (fun key z => g key (label z)) (fun key z => a key (label z))
  apply lt_of_le_of_lt _ hcap
  apply event_mono_on_support _ _ _ hraw.1
  intro y _hy hbad
  exact alignment_native_cylinder_failure_original_product (κ := κ) D n v hv label slots l.prod B L
    obs (fun z => (hB z).2) hpresentation F q₀ w T d
    (shift (alignmentShortExposureKey F w i T y))
    (g (alignmentShortExposureKey F w i T y)) (a (alignmentShortExposureKey F w i T y)) c C τ y hbad

end Hindman168
