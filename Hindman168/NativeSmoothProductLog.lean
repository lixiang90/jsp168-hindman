import Hindman168.NativeSequentialAdaptedFactorization
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Data.List.OfFn

/-! The actual native product logarithm and every finite ordered product
are smooth in their original real vector inputs. All identities use the
original exponential/logarithm; no BCH smoothness oracle or extra metric
on the group is supplied. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeSmoothProductLog {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (v w : D.E) : D.E :=
  nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w)

theorem native_smooth_product_log_contDiff {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) :
    ContDiff ℝ ∞ (fun p : D.E × D.E => nativeSmoothProductLog D p.1 p.2) := by
  have hf : ContMDiff 𝓘(ℝ, D.E × D.E) 𝓘(ℝ, D.E) ∞ (fun p : D.E × D.E => p.1) := contDiff_fst.contMDiff
  have hs : ContMDiff 𝓘(ℝ, D.E × D.E) 𝓘(ℝ, D.E) ∞ (fun p : D.E × D.E => p.2) := contDiff_snd.contMDiff
  exact ((nativeLieGlobalLogarithm_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp
    (((nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp hf).mul
      ((nativeLieExponential_contMDiff (E := D.E) (I := D.I) (G := D.G)).comp hs))).contDiff

noncomputable def nativeSmoothOrderedLog {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) : List D.E → D.E
  | [] => 0
  | v :: vs => nativeSmoothProductLog D v (nativeSmoothOrderedLog D vs)

theorem native_smooth_ordered_log_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (vs : List D.E) :
    nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (nativeSmoothOrderedLog D vs) =
      (vs.map (fun v : D.E => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v)).prod := by
  induction vs with
  | nil => exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)
  | cons v vs ih =>
      have he := nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
          nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (nativeSmoothOrderedLog D vs))
      exact he.trans (congrArg (fun g : D.G => nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v * g) ih)

theorem native_smooth_ordered_log_contDiff {s : ℕ} {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : NativeNilmanifoldData.{u} s) (N : ℕ) (v : Fin N → X → D.E)
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) :
    ContDiff ℝ ∞ (fun x => nativeSmoothOrderedLog D (List.ofFn (fun i => v i x))) := by
  induction N with
  | zero =>
      simp only [List.ofFn_zero, nativeSmoothOrderedLog]
      exact contDiff_const
  | succ N ih =>
      simp only [List.ofFn_succ, nativeSmoothOrderedLog]
      exact (native_smooth_product_log_contDiff D).comp
        ((hv 0).prodMk (ih (fun i => v i.succ) (fun i => hv i.succ)))

end Hindman168
