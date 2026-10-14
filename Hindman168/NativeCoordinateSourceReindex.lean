import Hindman168.RoughVectorMvSubstitution
import Hindman168.NativeResidualSource
import Hindman168.RoughCoordinateSamplingReindex

/-! Rename spatial coordinates while retaining the removed parameter NONE.
Actual native sources and vector polynomials undergo the SAME substitution;
degree, all-real log and spatial residue normalization are preserved. -/
namespace Hindman168
universe u

def roughNativeCoordinateSource {κ τ : Type*} {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (e : κ ≃ τ) (Q : (Option κ → ℝ) → D.G) : (Option τ → ℝ) → D.G :=
  fun x => Q (fun j => x (Option.map e j))

noncomputable def roughNativeCoordinatePolynomial {κ τ E : Type*} (e : κ ≃ τ)
    (p : RoughVectorMvPolynomial (Option κ) E) : RoughVectorMvPolynomial (Option τ) E :=
  roughVectorMvSubstitution (fun j => MvPolynomial.X (Option.map e j)) p

theorem rough_native_coordinate_polynomial_degree {κ τ E : Type*} (e : κ ≃ τ)
    {p : RoughVectorMvPolynomial (Option κ) E} {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    RoughVectorMvDegreeLE (roughNativeCoordinatePolynomial e p) d := by
  exact rough_vector_mv_substitution_degree _ (fun _ => by simp) hp

theorem rough_native_coordinate_polynomial_eval {κ τ E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : κ ≃ τ)
    (p : RoughVectorMvPolynomial (Option κ) E) (z : ℝ) (y : τ → ℝ) :
    roughVectorMvEval (roughNativeCoordinatePolynomial e p) (Option.elim · z y) =
      roughVectorMvEval p (Option.elim · z (fun j => y (e j))) := by
  rw [roughNativeCoordinatePolynomial,rough_vector_mv_substitution_eval]
  congr 1
  funext j
  cases j <;> simp only [MvPolynomial.eval_X,Option.map_none,Option.map_some,Option.elim_none,Option.elim_some]

theorem rough_native_coordinate_source_log {κ τ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (e : κ ≃ τ) (Q : (Option κ → ℝ) → D.G)
    (p : RoughVectorMvPolynomial (Option κ) D.E)
    (hlog : ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (Q (Option.elim · z y))) :
    ∀ (z : ℝ) (y : τ → ℝ), roughVectorMvEval (roughNativeCoordinatePolynomial e p) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (roughNativeCoordinateSource D e Q (Option.elim · z y)) := by
  intro z y
  rw [rough_native_coordinate_polynomial_eval,hlog]
  congr 2
  funext j
  cases j <;> rfl

theorem rough_native_coordinate_residual_source {κ τ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (e : κ ≃ τ) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q : ℕ) :
    roughNativeResidualSource D (roughNativeCoordinateSource D e Q) (fun j => a (e.symm j)) q =
      roughNativeCoordinateSource D e (roughNativeResidualSource D Q a q) := by
  funext x
  unfold roughNativeResidualSource roughNativeCoordinateSource
  congr 1
  funext j
  cases j <;> simp only [Option.map_none,Option.map_some,Option.elim_none,Option.elim_some,Equiv.symm_apply_apply]

end Hindman168
