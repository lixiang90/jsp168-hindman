import Hindman168.NativeResidualLargeEvent
import Hindman168.NativeFiniteRoughProportion

/-! Residual-factor removal for the ORIGINAL Q, retained a/q and actual
coarse/fine samples. The polynomial premise is the manuscript's literal
all-real normalized log identity; an actual raw polynomial also supplies it.
One threshold precedes q/a, all sources and every varying sampling witness. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

def NativeResidualRoughProportionBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d w R : ℕ) (Scale Z c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ modulus r : ℕ, 0 < modulus →
    (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
    primorial w ∣ modulus → (primorial w).Coprime r →
    (R : ℝ) ≤ Scale/(modulus : ℝ) →
    ∀ (q : ℕ) (a : Fin n → ℤ), 0 < q →
    ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (pN : RoughVectorMvPolynomial (Option (Fin n)) D.E),
    RoughVectorMvDegreeLE pN d →
    (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval pN (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (roughNativeResidualSource D Q a q (Option.elim · z y))) →
    (((roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeResidualComplexLargeIndex D Q a q t t Z c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ)

theorem native_original_to_residual_rough_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w R : ℕ)
    (Scale Z c C B η δ : ℝ) (L : NNReal)
    (h : NativeOriginalRoughProportionBound D n d w R Scale Z c C B η δ L) :
    NativeResidualRoughProportionBound D n d w R Scale Z c C B η δ L := by
  intro modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN
  have hnormalized := h modulus r hm hs hW hr hratio
    (roughNativeResidualSource D Q a q) pN hpN hlogN
  have hsub : (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeResidualComplexLargeIndex D Q a q t t Z c C L B η) ⊆
      (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeComplexLargeIndex D (roughNativeResidualSource D Q a q) t t Z c C L B η) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨ht,
      rough_native_residual_large_event_normalize D Q a q t t hq Z c C L B η hbad⟩
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hnormalized

theorem native_residual_rough_bound_raw_source {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w R : ℕ)
    (Scale Z c C B η δ : ℝ) (L : NNReal)
    (h : NativeResidualRoughProportionBound D n d w R Scale Z c C B η δ L)
    (modulus r : ℕ) (hm : 0 < modulus)
    (hs : ∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w)
    (hW : primorial w ∣ modulus) (hr : (primorial w).Coprime r)
    (hratio : (R : ℝ) ≤ Scale/(modulus : ℝ))
    (q : ℕ) (a : Fin n → ℤ) (hq : 0 < q)
    (Q : (Option (Fin n) → ℝ) → D.G) (p : RoughVectorMvPolynomial (Option (Fin n)) D.E)
    (hp : RoughVectorMvDegreeLE p d)
    (hlog : ∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) :
    (((roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeResidualComplexLargeIndex D Q a q t t Z c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ) :=
  h modulus r hm hs hW hr hratio q a hq Q (roughNativeResidualPolynomial p a q)
    (rough_native_residual_polynomial_degree hp a q) (rough_native_residual_source_log D Q p a q hlog)

theorem native_residual_rough_proportion_uniform {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop,
      NativeResidualRoughProportionBound D n d w R (Scale w) (Z w) c C B η δ L := by
  obtain ⟨R,hR,hbound⟩ := native_original_rough_proportion_uniform D n d c C B η L
    hc hB hη Scale Z hScale hg hδ
  exact ⟨R,hR,hbound.mono (fun w hw =>
    native_original_to_residual_rough_bound D n d w R _ _ _ _ _ _ _ L hw)⟩

theorem native_finite_residual_rough_proportion_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop, ∀ i : ι,
      NativeResidualRoughProportionBound (D i) n d w R (Scale w) (Z w) c C B η δ L := by
  obtain ⟨R,hR,hbound⟩ := native_finite_original_rough_proportion_uniform D n d c C B η L
    hc hB hη Scale Z hScale hg hδ
  exact ⟨R,hR,hbound.mono (fun w hw i =>
    native_original_to_residual_rough_bound (D i) n d w R _ _ _ _ _ _ _ L (hw i))⟩

theorem native_finite_residual_rough_fraction_tendsto {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop)
    (modulus r q : ℕ → ℕ) (a : ℕ → Fin n → ℤ)
    (hm : ∀ᶠ w in atTop, 0 < modulus w) (hq : ∀ᶠ w in atTop, 0 < q w)
    (hs : ∀ᶠ w in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus w → prime ≤ w)
    (hW : ∀ᶠ w in atTop, primorial w ∣ modulus w)
    (hr : ∀ᶠ w in atTop, (primorial w).Coprime (r w))
    (hratio : Tendsto (fun w => Scale w/(modulus w : ℝ)) atTop atTop)
    (Q : ∀ w, (Option (Fin n) → ℝ) → (D (index w)).G)
    (pN : ∀ w, RoughVectorMvPolynomial (Option (Fin n)) (D (index w)).E)
    (hpN : ∀ w, RoughVectorMvDegreeLE (pN w) d)
    (hlogN : ∀ w (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (pN w) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D (index w)).E) (I := (D (index w)).I)
        (roughNativeResidualSource (D (index w)) (Q w) (a w) (q w) (Option.elim · z y))) :
    Tendsto (fun w =>
      (((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeResidualComplexLargeIndex (D (index w)) (Q w) (a w) (q w) t t
          (Z w) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [] with w
    apply lt_of_lt_of_le hb
    positivity
  · intro δ hδ
    obtain ⟨R,_hR,hbound⟩ := native_finite_residual_rough_proportion_uniform D n d c C B η L
      hc hB hη Scale Z hScale hg hδ
    filter_upwards [hbound,hm,hq,hs,hW,hr,hratio.eventually (eventually_ge_atTop (R : ℝ))]
      with w hw hmw hqw hsw hWw hrw hRw
    have he := hw (index w) (modulus w) (r w) hmw hsw hWw hrw hRw
      (q w) (a w) hqw (Q w) (pN w) (hpN w) (hlogN w)
    have hcard : (0 : ℝ) < (roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card := by
      have hn : (0 : ℝ) ≤ (Finset.card ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeResidualComplexLargeIndex (D (index w)) (Q w) (a w) (q w) t t
          (Z w) c C L B η)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact (div_lt_iff₀ hcard).mpr (by simpa only [mul_comm] using he)

end Hindman168
