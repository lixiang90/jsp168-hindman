import Hindman168.NativeFinitePiData
import Hindman168.SingletonChartNativeExponential

/-! Native exponential/logarithm of the genuine finite product are exactly
the original component exponentials/logarithms. The coordinate product chart
is identified by ODE uniqueness, not by an assumed compatibility rule. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

noncomputable def nativeFinitePiExponentialHomeomorph {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) :
    (nativeFinitePiData D).E ≃ₜ (nativeFinitePiData D).G := by
  change (∀ i, (D i).E) ≃ₜ (∀ i, (D i).G)
  exact finitePiGroupHomeomorph (fun i =>
    nativeLieExponentialDiffeomorph (E := (D i).E) (I := (D i).I) (G := (D i).G))

theorem native_finite_pi_homeomorph_coordinate {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (x : (nativeFinitePiData D).E) (i : ι) :
    nativeFinitePiGroupEquiv D (nativeFinitePiExponentialHomeomorph D x) i =
      nativeLieExponentialDiffeomorph (E := (D i).E) (I := (D i).I) (G := (D i).G)
        (nativeFinitePiModelEquiv D x i) := rfl

theorem native_finite_pi_homeomorph_zero {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) : nativeFinitePiExponentialHomeomorph D 0=1 := by
  apply (nativeFinitePiGroupEquiv D).injective
  funext i
  rw [native_finite_pi_homeomorph_coordinate, map_zero, map_one]
  letI : LieGroup (D i).I (minSmoothness ℝ 3) (D i).G := lieGroup_smooth_min_three
  exact nativeLieExponential_zero (E := (D i).E) (I := (D i).I) (G := (D i).G)

theorem native_finite_pi_homeomorph_ray_add {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (x : (nativeFinitePiData D).E) (r t : ℝ) :
    nativeFinitePiExponentialHomeomorph D ((r+t) • x) =
      nativeFinitePiExponentialHomeomorph D (r • x)*nativeFinitePiExponentialHomeomorph D (t • x) := by
  apply (nativeFinitePiGroupEquiv D).injective
  funext i
  simp only [map_mul,Pi.mul_apply,native_finite_pi_homeomorph_coordinate,map_smul,Pi.smul_apply]
  letI : LieGroup (D i).I (minSmoothness ℝ 3) (D i).G := lieGroup_smooth_min_three
  exact nativeLieExponential_add_smul (E := (D i).E) (I := (D i).I) (G := (D i).G)
    (nativeFinitePiModelEquiv D x i) r t

theorem native_finite_pi_native_exponential {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) :
    let A := nativeFinitePiData D
    letI : LieGroup A.I (minSmoothness ℝ 3) A.G := lieGroup_smooth_min_three
    ∀ x : A.E, nativeLieExponential (E := A.E) (I := A.I) (G := A.G) x=
      nativeFinitePiExponentialHomeomorph D x :=
  homeomorph_singleton_native_exponential (nativeFinitePiExponentialHomeomorph D) (nativeFinitePiData D).lie
    (native_finite_pi_homeomorph_zero D) (native_finite_pi_homeomorph_ray_add D)

theorem native_finite_pi_native_logarithm {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (g : (nativeFinitePiData D).G) :
    nativeLieGlobalLogarithm (E := (nativeFinitePiData D).E) (I := (nativeFinitePiData D).I)
      (G := (nativeFinitePiData D).G) g = (nativeFinitePiExponentialHomeomorph D).symm g :=
  homeomorph_singleton_native_logarithm (nativeFinitePiExponentialHomeomorph D) (nativeFinitePiData D).lie
    (native_finite_pi_homeomorph_zero D) (native_finite_pi_homeomorph_ray_add D) g

theorem native_finite_pi_log_coordinate {ι : Type} [Fintype ι] {s : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (g : (nativeFinitePiData D).G) (i : ι) :
    nativeFinitePiModelEquiv D (nativeLieGlobalLogarithm (E := (nativeFinitePiData D).E)
      (I := (nativeFinitePiData D).I) (G := (nativeFinitePiData D).G) g) i =
    nativeLieGlobalLogarithm (E := (D i).E) (I := (D i).I) (G := (D i).G) (nativeFinitePiGroupEquiv D g i) := by
  rw [native_finite_pi_native_logarithm]
  rfl

end Hindman168
