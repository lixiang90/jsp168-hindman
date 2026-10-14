import Hindman168.AlignmentNativeWindowAllAnchors
import Hindman168.NativeRealResidualEventReindex

/-! Apply the existing proved native window cap to ANY actual finite spatial
index type, preserving the free removed parameter, all samples and log packet. -/
namespace Hindman168
universe u
open FiniteMass

theorem alignment_native_window_cap_coordinate {s : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (D : ι → NativeNilmanifoldData.{u} s)
    (m degree : ℕ) (e : κ ≃ Fin m) {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (U : Finset (Fin n)) (j : T) (denominator : ℕ)
    (Kref K c C B η δ : ℝ) (L : NNReal)
    (hcap : AlignmentNativeWindowCap D m degree F w i T x U j
      denominator Kref K c C B η δ L)
    (index : ι) (q : ℕ) (a : κ → ℤ) (hq : 0 < q)
    (Q : (Option κ → ℝ) → (D index).G)
    (pN : RoughVectorMvPolynomial (Option κ) (D index).E)
    (hp : RoughVectorMvDegreeLE pN degree)
    (hlog : ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pN (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D index).E) (I := (D index).I)
        (roughNativeResidualSource (D index) Q a q (Option.elim · z y)))
    (Zactual : ℕ → ℝ)
    (hZ : ∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val),
      alignmentCubeScale F w i T x /
        ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref) ≤ Zactual t ∧
      Zactual t ≤ K*(alignmentCubeScale F w i T x /
        ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref))) :
    event (uniformFinsetMass
      (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
      (fun t => RoughNativeRealResidualComplexLargeIndex (D index) Q a q t t
        (Zactual t) c C L B η) < δ := by
  have hp' := rough_native_coordinate_polynomial_degree e hp
  have hlog' := rough_native_coordinate_source_log (D index) e
    (roughNativeResidualSource (D index) Q a q) pN hlog
  rw [←rough_native_coordinate_residual_source] at hlog'
  have hh := hcap index q (fun j => a (e.symm j)) hq
    (roughNativeCoordinateSource (D index) e Q) (roughNativeCoordinatePolynomial e pN)
    hp' hlog' Zactual hZ
  apply lt_of_le_of_lt _ hh
  exact event_mono _ (uniformFinsetMass_nonneg _) (fun t ht =>
    rough_native_real_residual_event_reindex (D index) e Q a q t t (Zactual t) c C L B η ht)

end Hindman168
