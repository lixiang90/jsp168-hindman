import Hindman168.NativeDyadicExceptionalDensity
import Hindman168.RoughNativeComplexLargeIndex

/-! The original rough-step exceptional-proportion conclusion, for complex
observables, non-strict discrepancy, actual dyadic residue sets and arbitrary
varying joint logarithmic polynomials. Samples are genuinely nonempty.
This is not a Gowers correlation inverse or a final FS/FP theorem. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

def NativeOriginalRoughProportionBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d w R : ℕ) (Scale Z c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ modulus r : ℕ, 0 < modulus →
    (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
    primorial w ∣ modulus → (primorial w).Coprime r →
    (R : ℝ) ≤ Scale/(modulus : ℝ) →
    ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
    RoughVectorMvDegreeLE p d →
    (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) →
    (((roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeComplexLargeIndex D Q t t Z c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ)

theorem native_original_rough_proportion_uniform {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop,
      NativeOriginalRoughProportionBound D n d w R (Scale w) (Z w) c C B η δ L := by
  have hsmall : 0 < η/4 := div_pos hη (by norm_num)
  obtain ⟨R,hR,hbound⟩ := native_dyadic_exceptional_density D n d c (max 1 C) B (η/4) L
    hc (le_max_left _ _) hB hsmall Scale Z hScale hg hδ
  have hZ : ∀ᶠ w in atTop, 0 ≤ Z w := by
    filter_upwards [hScale.eventually (eventually_ge_atTop 1),
      (hg 1 (by norm_num)).eventually (eventually_ge_atTop 0)] with w hS hz
    have hSp : 0 < Scale w := zero_lt_one.trans_le hS
    have hdiv : 0 ≤ Z w/Scale w := by simpa only [Real.rpow_one] using hz
    simpa only [zero_mul] using (le_div_iff₀ hSp).mp hdiv
  refine ⟨R,hR,?_⟩
  filter_upwards [hbound,hZ] with w hw hz
  intro modulus r hm hs hW hr hratio Q p hp hlog
  have hreal := hw modulus r hm hs hW hr hratio Q p hp hlog
  have hsub : (roughDyadicResidueSteps (Scale w) modulus r).filter
      (fun t => RoughNativeComplexLargeIndex D Q t t (Z w) c C L B η) ⊆
      (roughDyadicResidueSteps (Scale w) modulus r).filter
      (fun t => RoughNativeBadIndex D Q t t (Z w) c (max 1 C) L B (η/4)) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨ht,rough_native_bad_index_mono D Q hz (le_max_right 1 C)
      (rough_native_complex_large_index_real D Q t t (Z w) c C L B η hη hbad)⟩
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hreal

theorem native_original_rough_bad_fraction_tendsto {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    (modulus r : ℕ → ℕ)
    (hmod : ∀ᶠ w in atTop, 0 < modulus w)
    (hsmooth : ∀ᶠ w in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus w → prime ≤ w)
    (hW : ∀ᶠ w in atTop, primorial w ∣ modulus w)
    (hr : ∀ᶠ w in atTop, (primorial w).Coprime (r w))
    (hratio : Tendsto (fun w => Scale w/(modulus w : ℝ)) atTop atTop)
    (Q : ℕ → (Option (Fin n) → ℝ) → D.G)
    (p : ℕ → RoughVectorMvPolynomial (Option (Fin n)) D.E)
    (hp : ∀ w, RoughVectorMvDegreeLE (p w) d)
    (hlog : ∀ w (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (p w) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q w (Option.elim · z y))) :
    Tendsto (fun w =>
      (((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeComplexLargeIndex D (Q w) t t (Z w) c C L B η)).card : ℝ) /
        ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with w
    apply lt_of_lt_of_le ha
    positivity
  · intro δ hδ
    obtain ⟨R,_hR,hbound⟩ := native_original_rough_proportion_uniform D n d c C B η L
      hc hB hη Scale Z hScale hg hδ
    filter_upwards [hbound,hmod,hsmooth,hW,hr,hratio.eventually (eventually_ge_atTop (R : ℝ))]
      with w hw hm hs hWw hrw hR
    have he := hw (modulus w) (r w) hm hs hWw hrw hR (Q w) (p w) (hp w) (hlog w)
    have hcard : (0 : ℝ) < (roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card := by
      have hn : (0 : ℝ) ≤ (Finset.card ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeComplexLargeIndex D (Q w) t t (Z w) c C L B η)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact (div_lt_iff₀ hcard).mpr (by simpa only [mul_comm] using he)

end Hindman168
