import Hindman168.WeightedShearNativeHaar
import Hindman168.AffineShearNativeInitialLayer
import Hindman168.NativeRationalLayerHaarImage

/-!
The original joint `h H rho Gamma/Gamma` Haar limit. The basis and coordinate
weights are constructed inside the actual proper level-one subgroup, and the
probability is pushed through its actual conjugate-lattice orbit map.
-/
namespace Hindman168
open MeasureTheory Filter Module
open scoped Topology Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- The harmless total-parameter convention is exactly the original law on expanding boxes. -/
theorem weightedShearBoxProbability_actual_law {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (E : ℝ) (hE : 1 ≤ E) :
    (weightedShearBoxProbability w E).toMeasure = weightedShearBoxLaw w E := by
  change weightedShearBoxLaw w (max E 1) = _
  rw [max_eq_left hE]

/-- The original orbit map remains continuous for both specified quotient metrics. -/
theorem weightedShear_joint_orbit_map_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (h : D.G) :
    let A := nativeRationalLayerOrbitData D F 1 ρ hρ
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    Continuous (nativeRationalLayerOrbitMap D F 1 ρ hρ h) := by
  let A := nativeRationalLayerOrbitData D F 1 ρ hρ
  have hc : @Continuous (A.G ⧸ A.Γ) (D.G ⧸ D.Γ)
      (QuotientGroup.instTopologicalSpace A.Γ) (QuotientGroup.instTopologicalSpace D.Γ)
      (nativeRationalLayerOrbitMap D F 1 ρ hρ h) :=
    native_rational_layer_orbit_map_continuous D F 1 ρ hρ h
  rw [nativeNilmanifold_metric_topology A, nativeNilmanifold_metric_topology D] at hc
  exact hc

/-- Actual boxes after a fixed joint shear, projected to the original joint orbit. -/
noncomputable def weightedShearJointOrbitBoxProbability {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E)
    (w : Fin n → ℕ) (h : D.G) (f : weightedShearGroup (R := ℝ) w) (E : ℝ) :
    letI : MeasurableSpace D.G := borel D.G
    ProbabilityMeasure (D.G ⧸ D.Γ) := by
  let A := nativeRationalLayerOrbitData D F 1 ρ hρ
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  exact (weightedShearNativeShearedBoxProbability A w b f E).map
    (weightedShear_joint_orbit_map_continuous D F ρ hρ h).measurable.aemeasurable

/-- For every expanding parameter, the joint law is literally the image of the
original normalized box under the original orbit map after the specified shear. -/
theorem weightedShearJointOrbitBoxProbability_actual_law {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E)
    (w : Fin n → ℕ) (h : D.G) (f : weightedShearGroup (R := ℝ) w)
    (E : ℝ) (hE : 1 ≤ E) :
    letI : MeasurableSpace D.G := borel D.G
    (weightedShearJointOrbitBoxProbability D F ρ hρ b w h f E).toMeasure =
      Measure.map (fun x => nativeRationalLayerOrbitMap D F 1 ρ hρ h
        (weightedShearNativeProjection (nativeRationalLayerOrbitData D F 1 ρ hρ) b (f • x)))
        (weightedShearBoxLaw w E) := by
  let A := nativeRationalLayerOrbitData D F 1 ρ hρ
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  have hc : Continuous (fun x => weightedShearNativeProjection A b (f • x)) :=
    (weightedShearNativeProjection_continuous A b).comp (weightedShearPoint_continuous f.val)
  change Measure.map (nativeRationalLayerOrbitMap D F 1 ρ hρ h)
    (Measure.map (fun x => weightedShearNativeProjection A b (f • x))
      (weightedShearBoxLaw w (max E 1))) = _
  rw [max_eq_left hE, Measure.map_map
    (weightedShear_joint_orbit_map_continuous D F ρ hρ h).measurable hc.measurable]
  rfl

/-- The original orbit limit for any fixed adapted basis. In particular the basis
can be exactly the one already used for the joint affine lifts. -/
theorem weightedShear_joint_orbit_haar_tendsto_of_adapted_basis {s ℓ n : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E) (w : Fin n → ℕ)
    (hw : ∀ i, 1 ≤ w i ∧ w i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration D F ρ hρ (w i) ∧
      affineShearNativeInitialFiltration D F ρ hρ (w i+1) ≤ (b.coord i).ker)
    (h : D.G) (f : weightedShearGroup (R := ℝ) w) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    Tendsto (weightedShearJointOrbitBoxProbability D F ρ hρ b w h f) atTop
      (𝓝 (⟨nativeRationalLayerHaarImage D F 1 ρ hρ h,
        native_rational_layer_haar_image_isProbability D F 1 ρ hρ h⟩ :
          ProbabilityMeasure (D.G ⧸ D.Γ))) := by
  let A := nativeRationalLayerOrbitData D F 1 ρ hρ
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  have hlim := weightedShear_native_sheared_box_haar_tendsto A w ℓ
    (fun i => (hw i).2.1) (fun i => (hw i).1)
    (affineShearNativeInitialFiltration D F ρ hρ)
    (affineShear_native_initial_antitone D F ρ hρ)
    (affineShear_native_initial_one D F ρ hρ)
    (affineShear_native_initial_bracket D F ρ hρ) b
    (fun i => (hw i).2.2.1) (fun i z hz => (hw i).2.2.2 hz) f
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (weightedShearNativeShearedBoxProbability A w b f)
    ⟨nativeNilmanifoldQuotientProbability A, native_nilmanifold_quotient_probability_isProbability A⟩
    hlim (weightedShear_joint_orbit_map_continuous D F ρ hρ h)

/-- With the original joint subgroup and conjugated lattice, one adapted coordinate
system gives the same full Haar-image limit after every fixed shear or word. -/
theorem weightedShear_joint_orbit_haar_tendsto {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E,
      ∃ w : Fin n → ℕ, (∀ i, 1 ≤ w i ∧ w i ≤ ℓ) ∧
      ∀ h : D.G, ∀ f : weightedShearGroup (R := ℝ) w,
        letI : MeasurableSpace D.G := borel D.G
        letI := D.metric
        letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
        letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
        Tendsto (weightedShearJointOrbitBoxProbability D F ρ hρ b w h f) atTop
          (𝓝 (⟨nativeRationalLayerHaarImage D F 1 ρ hρ h,
            native_rational_layer_haar_image_isProbability D F 1 ρ hρ h⟩ :
              ProbabilityMeasure (D.G ⧸ D.Γ))) := by
  obtain ⟨n, b, w, hw⟩ := affineShear_native_initial_adapted_basis D F ρ hρ
  refine ⟨n, b, w, fun i => ⟨(hw i).1, (hw i).2.1⟩, ?_⟩
  exact fun h f => weightedShear_joint_orbit_haar_tendsto_of_adapted_basis D F ρ hρ b w hw h f

end Hindman168
