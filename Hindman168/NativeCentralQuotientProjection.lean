import Hindman168.NativeCentralQuotientData

/-! ORIGINAL logarithm/exponential agree with the GENUINE new child data
under ORIGINAL quotient group and model projections. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u

attribute [local instance] lieGroup_smooth_min_three

theorem native_central_quotient_data_exponential {s : ℕ} (D : NativeNilmanifoldData.{u} s) (v : D.E) :
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v : D.G ⧸ Subgroup.center D.G) =
      nativeLieExponential (E := (nativeCentralQuotientData D).E)
        (I := (nativeCentralQuotientData D).I) (G := (nativeCentralQuotientData D).G)
        (nativeCenterQuotientProjection (I := D.I) (G := D.G) v) := by
  exact nativeCenterQuotient_nativeExponential_projection (I := D.I) (G := D.G) v

theorem native_central_quotient_data_logarithm {s : ℕ} (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    nativeLieGlobalLogarithm (E := (nativeCentralQuotientData D).E)
      (I := (nativeCentralQuotientData D).I) (G := (nativeCentralQuotientData D).G)
        (g : D.G ⧸ Subgroup.center D.G) =
      nativeCenterQuotientProjection (I := D.I) (G := D.G)
        (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) := by
  exact nativeCenterQuotient_nativeLogarithm_projection (I := D.I) (G := D.G) g

end Hindman168
