import Hindman168.RoughSpatialAffineSubstitution
import Hindman168.NativeNilmanifoldData

/-! Literal native source x=a+q*y, leaving the removed-factor parameter
unchanged. Retained a/q are fixed before that parameter varies. -/
namespace Hindman168
universe u

def roughNativeResidualSource {κ : Type*} {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (Q : (Option κ → ℝ) → D.G) (a : κ → ℤ) (q : ℕ) : (Option κ → ℝ) → D.G :=
  fun x => Q (Option.elim · (x none) (fun j => (a j : ℝ)+(q : ℝ)*x (some j)))

noncomputable def roughNativeResidualPolynomial {κ E : Type*}
    (p : RoughVectorMvPolynomial (Option κ) E) (a : κ → ℤ) (q : ℕ) :
    RoughVectorMvPolynomial (Option κ) E :=
  roughVectorMvAffineSubstitution (fun i => i.elim 0 (fun j => (a j : ℝ)))
    (fun i => i.elim 1 (fun _ => (q : ℝ))) p

theorem rough_native_residual_polynomial_degree {κ E : Type*}
    {p : RoughVectorMvPolynomial (Option κ) E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (a : κ → ℤ) (q : ℕ) :
    RoughVectorMvDegreeLE (roughNativeResidualPolynomial p a q) d :=
  roughVectorMvAffineSubstitution_degree _ _ hp

theorem rough_native_residual_source_log {κ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (p : RoughVectorMvPolynomial (Option κ) D.E) (a : κ → ℤ) (q : ℕ)
    (hlog : ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) :
    ∀ (z : ℝ) (y : κ → ℝ),
      roughVectorMvEval (roughNativeResidualPolynomial p a q) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (roughNativeResidualSource D Q a q (Option.elim · z y)) := by
  intro z y
  rw [roughNativeResidualPolynomial,rough_spatial_affine_vector_eval]
  simpa only [roughNativeResidualSource,Option.elim_none,Option.elim_some] using
    hlog z (fun j => (a j : ℝ)+(q : ℝ)*y j)

end Hindman168
