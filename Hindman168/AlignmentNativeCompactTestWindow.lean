import Hindman168.AlignmentNativeCoordinateWindowCap
import Hindman168.NativeRealResidualObservableApproximation

/-! Uniform compact-test bounds are chosen before original source/residue/
geometry and removed factor. Exact original family events are capped by the
proved native event, with the original full dyadic law and all raw anchors. -/
namespace Hindman168
universe u
open Filter FiniteMass

theorem alignment_native_window_cap_test_family {s : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (D : ι → NativeNilmanifoldData.{u} s)
    (m degree : ℕ) (e : κ ≃ Fin m) {n : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin n) (T : Finset (Fin n)) (x : Fin n → ℕ)
    (U : Finset (Fin n)) (j : T) (denominator : ℕ)
    (Kref K c C B η δ : ℝ) (L : NNReal) (hη : 0 < η)
    (hcap : AlignmentNativeWindowCap D m degree F w i T x U j
      denominator Kref K c C B (η/2) δ L)
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
    letI := (D index).metric
    letI : TopologicalSpace ((D index).G ⧸ (D index).Γ) :=
      (D index).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace ((D index).G ⧸ (D index).Γ) := native_metric_quotient_compact (D index)
    ∀ H : Set C((D index).G ⧸ (D index).Γ,ℂ),
    (∀ G ∈ H, ∃ A : C((D index).G ⧸ (D index).Γ,ℂ), LipschitzWith L A ∧
      (∀ y, ‖A y‖ ≤ B) ∧ ‖G-A‖ < η/4) →
    event (uniformFinsetMass
      (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
      (fun t => RoughNativeRealResidualTestFamilyLargeIndex (D index) Q a q t t
        (Zactual t) c C η H) < δ := by
  intro H happrox
  have hh := alignment_native_window_cap_coordinate D m degree e F w i T x U j
    denominator Kref K c C B (η/2) δ L hcap index q a hq Q pN hp hlog Zactual hZ
  apply lt_of_le_of_lt _ hh
  exact event_mono _ (uniformFinsetMass_nonneg _) (fun t ht =>
    rough_native_real_residual_test_family_approximation (D index) Q a q t t
      (Zactual t) c C η B L hη H happrox ht)

theorem alignment_native_compact_test_window_all_anchors {s : ℕ} {κ : Type*} [Fintype κ]
    (D : NativeNilmanifoldData.{u} s) (degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C η : ℝ) (hKref : 0 < Kref) (hK : 1 ≤ K)
    (hc : 0 < c) (hC : 0 ≤ C) (hη : 0 < η) {δ : ℝ} (hδ : 0 < δ) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (D.G ⧸ D.Γ) := native_metric_quotient_compact D
    ∀ H : Set C(D.G ⧸ D.Γ,ℂ), IsCompact H →
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
    ∀ᶠ w in atTop, ∀ x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support,
      alignmentTypicalShortPosterior F w i T x →
      ∀ U : Finset (Fin n), U ⊆ T → ∀ j : T,
      ∀ (q : ℕ) (a : κ → ℤ), 0 < q →
      ∀ (Q : (Option κ → ℝ) → D.G) (pN : RoughVectorMvPolynomial (Option κ) D.E),
      RoughVectorMvDegreeLE pN degree →
      (∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pN (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := D.E) (I := D.I)
          (roughNativeResidualSource D Q a q (Option.elim · z y))) →
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val),
        alignmentCubeScale F w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref) ≤ Zactual t ∧
        Zactual t ≤ K*(alignmentCubeScale F w i T x /
          ((denominator : ℝ)*alignmentNaturalBlockProduct x U*Kref))) →
      event (uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j.val)))
        (fun t => RoughNativeRealResidualTestFamilyLargeIndex D Q a q t t
          (Zactual t) c C η H) < δ := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro H hH
  obtain ⟨B,L,hB,hL,happrox⟩ := rough_native_real_residual_compact_family_bounds D η hη H hH
  refine ⟨B,L,hB,hL,?_⟩
  have hh := alignment_native_window_all_anchors_uniform (fun _ : Unit => D)
    (Fintype.card κ) degree hF i T hT denominator hdenominator Kref K c C B (η/2)
    (Real.toNNReal L) hKref hK hc hC hB.le (by positivity) hδ
  filter_upwards [hh] with w hw
  intro x hx htyp U hU j q a hq Q pN hp hlog Zactual hZ
  exact alignment_native_window_cap_test_family (fun _ : Unit => D)
    (Fintype.card κ) degree (Fintype.equivFin κ) F w i T x U j denominator
    Kref K c C B η δ (Real.toNNReal L) hη (hw x hx htyp U hU j)
    () q a hq Q pN hp hlog Zactual hZ H happrox

end Hindman168
