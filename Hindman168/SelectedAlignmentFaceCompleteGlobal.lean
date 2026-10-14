import Hindman168.AlignmentNativeCompleteCubeGlobal
import Hindman168.SelectedAlignmentFaceNativeFailure
import Hindman168.SelectedAlignmentFaceProductFailure
import Hindman168.SelectedAlignmentFaceDetection
import Hindman168.SelectedAlignmentFaceCylinderGlobal

namespace Hindman168
open Module Filter FiniteMass
open scoped Manifold ContDiff BigOperators Topology Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (r : ι → ℕ) (b : ∀ ν, Basis (Fin (r ν)) ℝ (alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)).E)

include n v hv r b in
theorem selected_alignment_native_complete_cube_all_faces_global_eventually
    {k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A P F) (gap : Fin N) (hgap : gap ≤ i)
    (q₀ : ℕ) (hq : 0 < q₀) (T : Finset (Fin N)) (hT : ∀ j ∈ T, j < gap)
    (d : ℕ) (hd : 0 < d) (c C : ℝ) (K : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : C+1 ≤ (K : ℝ))
    (B : ℝ) (L : NNReal) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ (shift : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ) →
        ι → AlignmentAddingPair N i → ℤ)
      (g a : ∀ _key : ((Fin N → ℕ) × (Fin N → ℕ) × (Fin N → ℕ) × ℕ × ℕ), ∀ ν, (D ν).G),
      event (globalRawMass (F.cutoff w) (primorial w) N)
        (fun y => selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv (alignmentGeometryWithGap F i gap) gap q₀ w T d
          (shift (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y))
          (g (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) (a (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) B L c C η y) < δ := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  obtain ⟨Q,τ,hτ,hQ,hdetect⟩ := selected_alignment_native_complete_cube_failure_finite_detection (κ := κ) D n v hv B L η hη
  let δ' := δ/((Q.card : ℝ)+1)
  have hδ' : 0 < δ' := by dsimp only [δ']; positivity
  have he : ((Q.card : ℝ)+1)*δ'=δ := by dsimp only [δ']; field_simp
  letI : Fintype Q := Fintype.ofFinite Q
  have hh (l : Q) := selected_alignment_native_cylinder_all_faces_global_eventually (κ := κ) D n v hv r b
    hF gap hgap q₀ hq T hT d hd c C K hc hC hK hτ hδ' l.val (hQ l.val l.property)
  have hall := Filter.eventually_all.mpr hh
  filter_upwards [hall,alignmentGlobalRawMass_geometry hF] with w hw hraw
  intro shift g a
  let μ := globalRawMass (F.cutoff w) (primorial w) N
  let E (l : List C(J.G ⧸ J.Γ,ℂ)) (y : Fin N → ℕ) :=
    selectedAlignmentNativeCylinderCubeAllFacesFailure (κ := κ) D n v hv (alignmentGeometryWithGap F i gap) gap q₀ w T d
      (shift (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y))
      (g (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) (a (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) c C τ l.prod y
  have hcap : event μ (fun y => ∃ l ∈ Q, E l y) ≤ (Q.card : ℝ)*δ' := by
    apply (event_union_bound μ Q E hraw.1).trans
    calc
      _ ≤ ∑ _l ∈ Q, δ' := Finset.sum_le_sum (fun l hl => (hw (⟨l,hl⟩ : Q) shift g a).le)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hmono : event μ
      (fun y => selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv (alignmentGeometryWithGap F i gap) gap q₀ w T d
        (shift (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y))
        (g (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) (a (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) B L c C η y) ≤
      event μ (fun y => ∃ l ∈ Q, E l y) := by
    apply event_mono_on_support _ _ _ hraw.1
    intro y _hy hbad
    exact hdetect (alignmentGeometryWithGap F i gap) gap q₀ w T d (shift (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y))
      (g (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) (a (alignmentShortExposureKey (alignmentGeometryWithGap F i gap) w i T y)) c C y hbad
  change event μ _ < δ
  nlinarith

end Hindman168
