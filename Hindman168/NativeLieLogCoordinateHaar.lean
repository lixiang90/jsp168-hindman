import Hindman168.NativeLogLeftTranslation
import Hindman168.NativeLieAdjointUnipotent
import Hindman168.SmoothUnitJacobianMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! EXPLICIT Haar measure on the ORIGINAL simply connected nilpotent Lie
group: push forward actual basis Lebesgue measure by the proved exponential.
Actual left/right/conjugation invariance is proved, not an existence hypothesis. -/

namespace Hindman168
open MeasureTheory Measure Module Function
open scoped Classical Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [IsTopologicalGroup G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieLogCoordinateHaar (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    Measure G := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace E := ⟨rfl⟩
  exact Measure.map (nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)) b.addHaar

theorem native_log_left_translation_basis_volume (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (g : G) :
    letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    Measure.map (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g) b.addHaar = b.addHaar := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact smooth_unit_jacobian_map_addHaar b.addHaar (nativeLogLeftTranslationHomeomorph (E := E) (I := I) g)
    ((native_log_left_translation_contDiff (I := I) g).differentiable (by norm_num))
    (native_log_left_translation_derivative_det_one (I := I) g)

omit [IsTopologicalGroup G] [SimplyConnectedSpace G] in
theorem native_adjoint_basis_volume (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (g : G) :
    letI : MeasurableSpace E := borel E
    letI : BorelSpace E := ⟨rfl⟩
    Measure.map (nativeLieAdjoint (E := E) (I := I) g) b.addHaar = b.addHaar := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have h := map_linearMap_addHaar_eq_smul_addHaar b.addHaar
    (f := (nativeLieAdjoint (E := E) (I := I) g).toLinearMap)
    (by rw [native_lie_adjoint_determinant_one]; norm_num)
  simpa only [ContinuousLinearMap.coe_coe, native_lie_adjoint_determinant_one, inv_one,
    abs_one, ENNReal.ofReal_one, one_smul] using h

theorem native_log_coordinate_haar_left_translation (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (g : G) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    Measure.map (fun x : G => g*x) (nativeLieLogCoordinateHaar (I := I) (G := G) b) =
      nativeLieLogCoordinateHaar (I := I) (G := G) b := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace E := ⟨rfl⟩
  letI : BorelSpace G := ⟨rfl⟩
  let e := nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)
  let T := nativeLogLeftTranslationHomeomorph (E := E) (I := I) g
  have hL : Measurable (fun x : G => g*x) := (Homeomorph.mulLeft g).measurable
  change Measure.map _ (Measure.map e b.addHaar) = Measure.map e b.addHaar
  rw [Measure.map_map hL e.measurable]
  have he : (fun x : G => g*x) ∘ e = e ∘ T := by
    funext v
    exact (nativeLieExponential_globalLogarithm (I := I) (g*e v)).symm
  rw [he, ← Measure.map_map e.measurable T.measurable,
    native_log_left_translation_basis_volume]

theorem native_log_coordinate_haar_conjugation (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (g : G) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    Measure.map (fun x : G => g*x*g⁻¹) (nativeLieLogCoordinateHaar (I := I) (G := G) b) =
      nativeLieLogCoordinateHaar (I := I) (G := G) b := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace E := ⟨rfl⟩
  letI : BorelSpace G := ⟨rfl⟩
  let e := nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)
  let A := nativeLieAdjoint (E := E) (I := I) g
  have hC : Measurable (fun x : G => g*x*g⁻¹) := (continuous_const.mul continuous_id).mul
    continuous_const |>.measurable
  change Measure.map _ (Measure.map e b.addHaar) = Measure.map e b.addHaar
  rw [Measure.map_map hC e.measurable]
  have he : (fun x : G => g*x*g⁻¹) ∘ e = e ∘ A := by
    funext v
    exact nativeLieAdjoint_exponential_conjugation (I := I) g v
  rw [he, ← Measure.map_map e.measurable A.continuous.measurable, native_adjoint_basis_volume]

theorem native_log_coordinate_haar_right_translation (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) (g : G) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    Measure.map (fun x : G => x*g) (nativeLieLogCoordinateHaar (I := I) (G := G) b) =
      nativeLieLogCoordinateHaar (I := I) (G := G) b := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace G := ⟨rfl⟩
  have hC : Measurable (fun x : G => g⁻¹*x*(g⁻¹)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hL : Measurable (fun x : G => g*x) := (Homeomorph.mulLeft g).measurable
  have he : (fun x : G => x*g) = (fun x : G => g*x) ∘ (fun x => g⁻¹*x*(g⁻¹)⁻¹) := by
    funext x
    simp only [comp_apply, inv_inv]
    group
  rw [he, ← Measure.map_map hL hC,
    native_log_coordinate_haar_conjugation, native_log_coordinate_haar_left_translation]

theorem native_log_coordinate_haar_isHaar (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    IsHaarMeasure (nativeLieLogCoordinateHaar (I := I) (G := G) b) := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace E := ⟨rfl⟩
  letI : BorelSpace G := ⟨rfl⟩
  let e := nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)
  exact { toIsFiniteMeasureOnCompacts := IsFiniteMeasureOnCompacts.map b.addHaar e
          toIsMulLeftInvariant := ⟨native_log_coordinate_haar_left_translation (I := I) b⟩
          toIsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective }

theorem native_log_coordinate_haar_isRightInvariant (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    IsMulRightInvariant (nativeLieLogCoordinateHaar (I := I) (G := G) b) := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  exact ⟨native_log_coordinate_haar_right_translation (I := I) b⟩

omit [IsTopologicalGroup G] in
theorem native_log_coordinate_haar_sigmaFinite (b : Basis (Fin (Module.finrank ℝ E)) ℝ E) :
    letI : MeasurableSpace E := borel E
    letI : MeasurableSpace G := borel G
    SigmaFinite (nativeLieLogCoordinateHaar (I := I) (G := G) b) := by
  letI : MeasurableSpace E := borel E
  letI : MeasurableSpace G := borel G
  letI : BorelSpace E := ⟨rfl⟩
  letI : BorelSpace G := ⟨rfl⟩
  exact (nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)).measurableEmbedding.sigmaFinite_map

end Hindman168
