import Hindman168.AlignmentNativeWindowSampling

/-! Native window caps under the actual master parameters. The analytic
budget is obtained from the proved finite-native-family theorem; all paper
growth, smoothness, rough units, density and normalizing mass are discharged.
Native polynomial packets and bounded geometry remain explicit raw inputs. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical
universe u

theorem alignment_native_actual_window_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (m degree : ℕ)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (denominator : ℕ) (hdenominator : 0 < denominator)
    (Kref K c C B η : ℝ) (L : NNReal)
    (hKref : 0 < Kref) (hK : 1 ≤ K) (hc : 0 < c) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 < η)
    (x : ℕ → Fin n → ℕ) (U : ℕ → Finset (Fin n)) (j : ℕ → T)
    (hvalid : ∀ᶠ w in atTop,
      x w ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      alignmentTypicalShortPosterior F w i T (x w) ∧ U w ⊆ T)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in atTop, ∀ index : ι,
      ∀ (q : ℕ) (a : Fin m → ℤ), 0 < q →
      ∀ (Q : (Option (Fin m) → ℝ) → (D index).G)
        (pN : RoughVectorMvPolynomial (Option (Fin m)) (D index).E),
      RoughVectorMvDegreeLE pN degree →
      (∀ (z : ℝ) (y : Fin m → ℝ), roughVectorMvEval pN (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (D index).E) (I := (D index).I)
          (roughNativeResidualSource (D index) Q a q (Option.elim · z y))) →
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x w (j w).val),
        alignmentCubeScale F w i T (x w) /
            ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref) ≤ Zactual t ∧
        Zactual t ≤ K*(alignmentCubeScale F w i T (x w) /
            ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref))) →
      event (uniformFinsetMass
        (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x w (j w).val)))
        (fun t => RoughNativeRealResidualComplexLargeIndex (D index) Q a q t t
          (Zactual t) c C L B η) < δ := by
  let Scale := fun w => ((2 ^ Nat.log2 (x w (j w).val) : ℕ) : ℝ)
  let Zref := fun w => alignmentCubeScale F w i T (x w) /
    ((denominator : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*Kref)
  have hScale := alignment_typical_native_factor_scale_tendsto hF i T x j
    (hvalid.mono (fun _ hw => hw.2.1))
  have hg := alignment_raw_native_reference_real_ratios hF i T hT denominator
    hdenominator Kref hKref x U (fun w => (j w).val)
    (hvalid.mono (fun _ hw => ⟨hw.1,hw.2.2,(j _).property⟩))
  obtain ⟨R,_hR,hbound⟩ := native_finite_real_residual_rough_proportion_uniform D m degree c (C*K)
    B η L hc (mul_nonneg hC (zero_le_one.trans hK)) hB hη Scale Zref hScale hg hδ
  have hratio := alignment_dyadic_residue_ratio_tendsto hF (fun w => (j w).val)
    (fun w => x w (j w).val) (hvalid.mono (fun _ hw =>
      (hw.2.1.1 (j _).val (j _).property).1.trans
        (Nat.log2_self_le (alignmentGlobalRawMass_support_positive hF _ _ hw.1 (j _).val).ne')))
  filter_upwards [hbound,hvalid,eventually_ge_atTop 1,
    hratio.eventually (eventually_ge_atTop (R : ℝ))] with w hw hv hwone hR
  intro index q a hq Q pN hpN hlogN Zactual hZrange
  exact alignment_native_variable_scale_window_event_lt (D index) m degree w R (Zref w)
    c C K B η δ L hF hwone (x w) hv.1 (j w).val hc.le hC hδ (hw index) hR
    q a hq Q pN hpN hlogN Zactual hZrange

end Hindman168
