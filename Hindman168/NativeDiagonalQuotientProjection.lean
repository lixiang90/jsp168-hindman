import Hindman168.NativeDiagonalProjectionSmooth
import Hindman168.NativeDiagonalQuotientData
import Hindman168.LieExponentialHomomorphism

/-! ACTUAL native diagonal model projection and ORIGINAL product/native
diagonal exponential-logarithm compatibility, via true smooth hom uniqueness. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three
attribute [local instance] diagonal_center_normal

noncomputable def nativeDiagonalGroupProjection {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeNilmanifoldProduct D D).G →* (nativeDiagonalQuotientData D).G :=
  QuotientGroup.mk' (diagonalCenterSubgroup D.G)

noncomputable def nativeDiagonalModelProjection {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    (nativeNilmanifoldProduct D D).E →L[ℝ] (nativeDiagonalQuotientData D).E := by
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  exact finiteRealQuotientProjection (nativeDiagonalCenterModel D)

theorem native_diagonal_quotient_data_exponential {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (v : (nativeNilmanifoldProduct D D).E) :
    nativeDiagonalGroupProjection D (nativeLieExponential (E := (nativeNilmanifoldProduct D D).E)
      (I := (nativeNilmanifoldProduct D D).I) (G := (nativeNilmanifoldProduct D D).G) v) =
      nativeLieExponential (E := (nativeDiagonalQuotientData D).E)
        (I := (nativeDiagonalQuotientData D).I) (G := (nativeDiagonalQuotientData D).G)
          (nativeDiagonalModelProjection D v) := by
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  letI := nativeDiagonalQuotientChartedSpace D
  let q := nativeDiagonalGroupProjection D
  have hq : MDifferentiable (nativeNilmanifoldProduct D D).I (nativeDiagonalQuotientData D).I q :=
    (native_diagonal_projection_contMDiff D).mdifferentiable (by norm_num)
  have hP : mfderiv (nativeNilmanifoldProduct D D).I (nativeDiagonalQuotientData D).I
      (q : (nativeNilmanifoldProduct D D).G → (nativeDiagonalQuotientData D).G) 1 = nativeDiagonalModelProjection D :=
    native_diagonal_projection_mfderiv D
  have h := nativeLieExponential_map (I := (nativeNilmanifoldProduct D D).I)
    (J := (nativeDiagonalQuotientData D).I) q hq v
  rw [hP] at h
  exact h

theorem native_diagonal_quotient_data_logarithm {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (g : (nativeNilmanifoldProduct D D).G) :
    nativeLieGlobalLogarithm (E := (nativeDiagonalQuotientData D).E)
      (I := (nativeDiagonalQuotientData D).I) (G := (nativeDiagonalQuotientData D).G)
        (nativeDiagonalGroupProjection D g) =
      nativeDiagonalModelProjection D (nativeLieGlobalLogarithm (E := (nativeNilmanifoldProduct D D).E)
        (I := (nativeNilmanifoldProduct D D).I) (G := (nativeNilmanifoldProduct D D).G) g) := by
  letI : IsClosed ((nativeDiagonalCenterModel D) : Set (D.E × D.E)) := native_diagonal_center_model_closed D
  have h := native_diagonal_quotient_data_exponential D
    (nativeLieGlobalLogarithm (E := (nativeNilmanifoldProduct D D).E)
      (I := (nativeNilmanifoldProduct D D).I) (G := (nativeNilmanifoldProduct D D).G) g)
  rw [nativeLieExponential_globalLogarithm (E := (nativeNilmanifoldProduct D D).E)] at h
  have h' := congrArg (nativeLieGlobalLogarithm (E := (nativeDiagonalQuotientData D).E)
    (I := (nativeDiagonalQuotientData D).I) (G := (nativeDiagonalQuotientData D).G)) h
  rw [nativeLieGlobalLogarithm_exponential (E := (nativeDiagonalQuotientData D).E)] at h'
  exact h'

end Hindman168
