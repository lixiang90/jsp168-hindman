import Hindman168.AlignmentNativeArrayNilmanifold
import Hindman168.AlignmentNativeCoefficientLog
import Hindman168.SingletonChartNativeExponential

/-! Identify the actual array coefficient logarithm with the native global
logarithm of its genuinely constructed nilmanifold. All charts and smooth
group structures come from the existing actual array construction. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def alignmentNativeArrayData {σ : Type} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (v : Fin (n+1) → σ → ℤ)
    (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v)) :
    NativeNilmanifoldData.{u} s := by
  letI := nativeFiniteProductNormedAddCommGroup (E := D.E) n
  letI := nativeFiniteProductNormedSpace (E := D.E) n
  letI := nativeFiniteProductCompleteSpace (E := D.E) n
  letI := nativeFiniteProductFiniteDimensional (E := D.E) n
  let V := alignmentNativeFiniteImageModel (E := D.E) (I := D.I) (G := D.G) n v
  let A := alignmentNativeAllIntegerArrayGroup (E := D.E) (I := D.I) (G := D.G) n v hv
  letI := alignmentNativeArrayChartedSpace (E := D.E) (I := D.I) (G := D.G) n v hv
  letI := alignmentNativeArray_lieGroup (E := D.E) (I := D.I) (G := D.G) n v hv
  letI := alignmentNativeArray_boundaryless (E := D.E) (I := D.I) (G := D.G) n v hv
  letI : IsTopologicalGroup A := topologicalGroup_of_lieGroup 𝓘(ℝ,V) ∞
  letI := alignmentNativeArrayGroup_contractible (E := D.E) (I := D.I) (G := D.G) n v hv
  letI := alignmentNativeArrayGroup_simplyConnected (E := D.E) (I := D.I) (G := D.G) n v hv
  letI := alignmentNativeArrayLattice_discrete (E := D.E) (I := D.I) (G := D.G) n v hv D.Γ
  letI := alignmentNativeArrayLattice_quotient_compact (E := D.E) (I := D.I) (G := D.G) n v hv D.Γ
  letI : Module ℚ V := Module.compHom _ (Rat.castHom ℝ)
  have hcut : (⊤ : Subgroup D.G).lowerCentralSeries s=⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr D.step_le
  letI := pointwiseArraySubgroup_nilpotent A s hcut
  let recipe := nativeNilmanifoldOfLie (E := V) (I := 𝓘(ℝ,V)) (G := A) s
    (pointwiseArraySubgroup_nilpotencyClass_le A s hcut) (pointwiseArrayLattice A D.Γ)
  exact {
    E := V
    H := V
    I := 𝓘(ℝ,V)
    G := A
    charted := alignmentNativeArrayChartedSpace (E := D.E) (I := D.I) (G := D.G) n v hv
    lie := alignmentNativeArray_lieGroup (E := D.E) (I := D.I) (G := D.G) n v hv
    boundaryless := alignmentNativeArray_boundaryless (E := D.E) (I := D.I) (G := D.G) n v hv
    step_le := pointwiseArraySubgroup_nilpotencyClass_le A s hcut
    Γ := pointwiseArrayLattice A D.Γ
    metric := recipe.metric
    metric_quotientMap := recipe.metric_quotientMap }

noncomputable def alignmentNativeArrayDataCoefficients {σ : Type} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (v : Fin (n+1) → σ → ℤ)
    (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v)) :
    letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
    (alignmentNativeArrayData D n v hv).E ≃ₗ[ℝ]
      alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra D.I D.G) := by
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  letI := nativeFiniteProductNormedAddCommGroup (E := D.E) n
  letI := nativeFiniteProductNormedSpace (E := D.E) n
  change alignmentNativeFiniteImageModel (E := D.E) (I := D.I) (G := D.G) n v ≃ₗ[ℝ]
    alignmentLiePolynomialArrays σ ℝ (GroupLieAlgebra D.I D.G)
  exact alignmentNativeArrayModelCoefficients (E := D.E) (I := D.I) (G := D.G) n v hv

def alignmentNativeArrayDataValue {σ : Type} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n : ℕ) (v : Fin (n+1) → σ → ℤ)
    (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))
    (a : alignmentNativeAllIntegerArrayGroup (E := D.E) (I := D.I) (G := D.G) n v hv) :
    (alignmentNativeArrayData D n v hv).G := a

variable {σ : Type} {s : ℕ} (D : NativeNilmanifoldData.{u} s)
  (n : ℕ) (v : Fin (n+1) → σ → ℤ)
  (hv : Function.Injective (alignmentNativeFiniteEvaluation (E := D.E) (I := D.I) (G := D.G) n v))

theorem alignment_array_exponential_zero :
    alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv
      (0 : (alignmentNativeArrayData D n v hv).E) = 1 := by
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  letI := nativeFiniteProductNormedAddCommGroup (E := D.E) n
  letI := nativeFiniteProductNormedSpace (E := D.E) n
  change alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv
    (0 : alignmentNativeFiniteImageModel (E := D.E) (I := D.I) (G := D.G) n v) = 1
  apply Subtype.ext
  funext z
  rw [alignmentNativeArrayExponential_evaluation]
  simp only [map_zero]
  exact nativeLieExponential_zero (I := D.I) (G := D.G)

theorem alignment_array_exponential_ray_add
    (x : (alignmentNativeArrayData D n v hv).E) (r t : ℝ) :
    alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv ((r+t) • x) =
      alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv (r • x) *
      alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv (t • x) := by
  letI : LieGroup D.I (minSmoothness ℝ 3) D.G := lieGroup_smooth_min_three
  letI := nativeFiniteProductNormedAddCommGroup (E := D.E) n
  letI := nativeFiniteProductNormedSpace (E := D.E) n
  let x' : alignmentNativeFiniteImageModel (E := D.E) (I := D.I) (G := D.G) n v := x
  change alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv ((r+t) • x') =
    alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv (r • x') *
    alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv (t • x')
  apply Subtype.ext
  funext z
  change (alignmentNativeArrayExponentialHomeomorph n v hv ((r+t) • x')).val z =
    (alignmentNativeArrayExponentialHomeomorph n v hv (r • x')).val z *
    (alignmentNativeArrayExponentialHomeomorph n v hv (t • x')).val z
  simp only [alignmentNativeArrayExponential_evaluation,map_smul]
  exact nativeLieExponential_add_smul (I := D.I) (G := D.G) _ r t

theorem alignment_array_native_exponential :
    let A := alignmentNativeArrayData D n v hv
    letI : LieGroup A.I (minSmoothness ℝ 3) A.G := lieGroup_smooth_min_three
    ∀ x : A.E, nativeLieExponential (I := A.I) (G := A.G) x =
      alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv x := by
  let A := alignmentNativeArrayData D n v hv
  let e : A.E ≃ₜ A.G := alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv
  exact homeomorph_singleton_native_exponential e A.lie
    (alignment_array_exponential_zero D n v hv) (alignment_array_exponential_ray_add D n v hv)

theorem alignment_array_native_logarithm
    (a : (alignmentNativeArrayData D n v hv).G) :
    nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
      (I := (alignmentNativeArrayData D n v hv).I) a =
    (alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv).symm a := by
  let A := alignmentNativeArrayData D n v hv
  let e : A.E ≃ₜ A.G := alignmentNativeArrayExponentialHomeomorph (E := D.E) (I := D.I) (G := D.G) n v hv
  exact homeomorph_singleton_native_logarithm e A.lie
    (alignment_array_exponential_zero D n v hv) (alignment_array_exponential_ray_add D n v hv) a

theorem alignment_array_native_coefficient_log
    (a : (alignmentNativeArrayData D n v hv).G) :
    alignmentNativeArrayModelCoefficients (E := D.E) (I := D.I) (G := D.G) n v hv
      (nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) a) =
      alignmentNativeCoefficientLog n v hv a := by
  rw [alignment_array_native_logarithm D n v hv]
  rfl

theorem alignment_array_data_coefficient_log
    (a : (alignmentNativeArrayData D n v hv).G) :
    alignmentNativeArrayDataCoefficients D n v hv
      (nativeLieGlobalLogarithm (E := (alignmentNativeArrayData D n v hv).E)
        (I := (alignmentNativeArrayData D n v hv).I) (G := (alignmentNativeArrayData D n v hv).G) a) =
      alignmentNativeCoefficientLog n v hv a := by
  exact alignment_array_native_coefficient_log D n v hv a

end Hindman168
