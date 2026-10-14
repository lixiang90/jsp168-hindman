import Hindman168.NativeRealResidualLargeEvent
import Hindman168.NativeResidualRoughProportion

/-! Genuine arbitrary REAL-box residual-factor comparison. Nonempty coarse
and fine samples are proved from growth, not assumed in the event definition.
Thresholds precede retained q/a, compatible fine residues and all raw sources. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

def NativeRealResidualRoughProportionBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
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
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t Z c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ)

theorem native_residual_to_real_residual_bound {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w R : ℕ)
    (Scale Z c C B η δ : ℝ) (L : NNReal) (hS : 1 ≤ Scale) (hZ : 1 ≤ Z)
    (hC : 0 ≤ C) (hlarge : 2 ≤ c*Z)
    (hsampling : ∀ t : ℕ, Scale ≤ (t : ℝ) → (t : ℝ) < 2*Scale →
      0 < t ∧ 4*(t : ℝ) ≤ c*Z)
    (h : NativeResidualRoughProportionBound D n d w R Scale Z (c/2) (2*(C+1)) B η δ L) :
    NativeRealResidualRoughProportionBound D n d w R Scale Z c C B η δ L := by
  intro modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN
  have hinteger := h modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN
  have hsub : (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t Z c C L B η) ⊆
      (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeResidualComplexLargeIndex D Q a q t t Z (c/2) (2*(C+1)) L B η) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    have hdyadic := (rough_dyadic_residue_steps_mem (zero_le_one.trans hS) modulus r t).mp ht
    obtain ⟨htpos,hstep⟩ := hsampling t hdyadic.1 hdyadic.2.1
    exact Finset.mem_filter.mpr ⟨ht,rough_native_real_residual_event_integer D Q a q t t hq htpos
      Z c C L B η hZ hC hlarge hstep hbad⟩
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hinteger

theorem native_finite_real_residual_rough_proportion_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Z w/(Scale w)^e) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop, ∀ i : ι,
      NativeRealResidualRoughProportionBound (D i) n d w R (Scale w) (Z w) c C B η δ L := by
  obtain ⟨R,hR,hbound⟩ := native_finite_residual_rough_proportion_uniform D n d (c/2) (2*(C+1)) B η L
    (div_pos hc (by norm_num)) hB hη Scale Z hScale hg hδ
  refine ⟨R,hR,?_⟩
  filter_upwards [hbound,rough_real_residual_sampling_thresholds c hc Scale Z hScale hg] with w hw hsampling
  intro i
  exact native_residual_to_real_residual_bound (D i) n d w R (Scale w) (Z w) c C B η δ L
    hsampling.1 hsampling.2.1 hC hsampling.2.2.1 hsampling.2.2.2 (hw i)

theorem native_finite_real_residual_rough_fraction_tendsto {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
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
        (fun t => RoughNativeRealResidualComplexLargeIndex (D (index w)) (Q w) (a w) (q w) t t
          (Z w) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [] with w
    apply lt_of_lt_of_le hb
    positivity
  · intro δ hδ
    obtain ⟨R,_hR,hbound⟩ := native_finite_real_residual_rough_proportion_uniform D n d c C B η L
      hc hC hB hη Scale Z hScale hg hδ
    filter_upwards [hbound,hm,hq,hs,hW,hr,hratio.eventually (eventually_ge_atTop (R : ℝ))]
      with w hw hmw hqw hsw hWw hrw hRw
    have he := hw (index w) (modulus w) (r w) hmw hsw hWw hrw hRw
      (q w) (a w) hqw (Q w) (pN w) (hpN w) (hlogN w)
    have hcard : (0 : ℝ) < (roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card := by
      have hn : (0 : ℝ) ≤ (Finset.card ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeRealResidualComplexLargeIndex (D (index w)) (Q w) (a w) (q w) t t
          (Z w) c C L B η)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact (div_lt_iff₀ hcard).mpr (by simpa only [mul_comm] using he)

end Hindman168
