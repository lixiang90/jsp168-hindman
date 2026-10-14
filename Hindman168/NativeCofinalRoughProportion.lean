import Hindman168.NativeRealOriginalRoughProportion
import Hindman168.RoughCofinalDataExtension
import Hindman168.RoughCofinalStrictSelection

/-! Arbitrary ACTUAL sieve-width sequences tending to infinity, including
repetitions and nonmonotonicity. Smoothness and primorial data use that actual
width, never a renamed sequence index. All original real-box/event data survive. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

theorem native_finite_real_residual_fraction_strict_cofinal {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (W : ℕ → ℕ) (hWstrict : StrictMono W)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun k => Z k/(Scale k)^e) atTop atTop)
    (modulus r q : ℕ → ℕ) (a : ℕ → Fin n → ℤ)
    (hm : ∀ᶠ k in atTop, 0 < modulus k) (hq : ∀ᶠ k in atTop, 0 < q k)
    (hs : ∀ᶠ k in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus k → prime ≤ W k)
    (hW : ∀ᶠ k in atTop, primorial (W k) ∣ modulus k)
    (hr : ∀ᶠ k in atTop, (primorial (W k)).Coprime (r k))
    (hratio : Tendsto (fun k => Scale k/(modulus k : ℝ)) atTop atTop)
    (Q : ∀ k, (Option (Fin n) → ℝ) → (D (index k)).G)
    (pN : ∀ k, RoughVectorMvPolynomial (Option (Fin n)) (D (index k)).E)
    (hpN : ∀ k, RoughVectorMvDegreeLE (pN k) d)
    (hlogN : ∀ k (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (pN k) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D (index k)).E) (I := (D (index k)).I)
        (roughNativeResidualSource (D (index k)) (Q k) (a k) (q k) (Option.elim · z y))) :
    Tendsto (fun k =>
      (((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).filter
        (fun t => RoughNativeRealResidualComplexLargeIndex (D (index k)) (Q k) (a k) (q k) t t
          (Z k) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).card : ℝ)) atTop (𝓝 0) := by
  let ScaleExt := roughCofinalExtension W Scale
  let ZExt := roughCofinalExtension W Z
  have hScaleExt := rough_cofinal_extension_tendsto W hWstrict Scale hScale
  have hGrowthExt := rough_cofinal_extension_paper_growth W hWstrict Scale Z hg
  apply tendsto_order.mpr
  constructor
  · intro b hb
    filter_upwards [] with k
    apply lt_of_lt_of_le hb
    positivity
  · intro δ hδ
    obtain ⟨R,_hR,hbound⟩ := native_finite_real_residual_rough_proportion_uniform D n d c C B η L
      hc hC hB hη ScaleExt ZExt hScaleExt hGrowthExt hδ
    have hAtWidth := hWstrict.tendsto_atTop.eventually hbound
    filter_upwards [hAtWidth,hm,hq,hs,hW,hr,hratio.eventually (eventually_ge_atTop (R : ℝ))]
      with k hw hmk hqk hsk hWk hrk hRk
    simp only [ScaleExt,ZExt,rough_cofinal_extension_at_sample W hWstrict] at hw
    have he := hw (index k) (modulus k) (r k) hmk hsk hWk hrk hRk
      (q k) (a k) hqk (Q k) (pN k) (hpN k) (hlogN k)
    have hcard : (0 : ℝ) < (roughDyadicResidueSteps (Scale k) (modulus k) (r k)).card := by
      have hn : (0 : ℝ) ≤ (Finset.card ((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).filter
        (fun t => RoughNativeRealResidualComplexLargeIndex (D (index k)) (Q k) (a k) (q k) t t
          (Z k) c C L B η)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact (div_lt_iff₀ hcard).mpr (by simpa only [mul_comm] using he)

theorem native_finite_real_residual_fraction_cofinal {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (W : ℕ → ℕ) (hWcofinal : Tendsto W atTop atTop)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun k => Z k/(Scale k)^e) atTop atTop)
    (modulus r q : ℕ → ℕ) (a : ℕ → Fin n → ℤ)
    (hm : ∀ᶠ k in atTop, 0 < modulus k) (hq : ∀ᶠ k in atTop, 0 < q k)
    (hs : ∀ᶠ k in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus k → prime ≤ W k)
    (hW : ∀ᶠ k in atTop, primorial (W k) ∣ modulus k)
    (hr : ∀ᶠ k in atTop, (primorial (W k)).Coprime (r k))
    (hratio : Tendsto (fun k => Scale k/(modulus k : ℝ)) atTop atTop)
    (Q : ∀ k, (Option (Fin n) → ℝ) → (D (index k)).G)
    (pN : ∀ k, RoughVectorMvPolynomial (Option (Fin n)) (D (index k)).E)
    (hpN : ∀ k, RoughVectorMvDegreeLE (pN k) d)
    (hlogN : ∀ k (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (pN k) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D (index k)).E) (I := (D (index k)).I)
        (roughNativeResidualSource (D (index k)) (Q k) (a k) (q k) (Option.elim · z y))) :
    Tendsto (fun k =>
      (((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).filter
        (fun t => RoughNativeRealResidualComplexLargeIndex (D (index k)) (Q k) (a k) (q k) t t
          (Z k) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).card : ℝ)) atTop (𝓝 0) := by
  apply rough_cofinal_tendsto_from_strict_subsequences W hWcofinal
  intro φ hφ hWφ
  exact native_finite_real_residual_fraction_strict_cofinal D (fun k => index (φ k))
    (W ∘ φ) hWφ n d c C B η L hc hC hB hη (Scale ∘ φ) (Z ∘ φ) (hScale.comp hφ.tendsto_atTop)
    (fun e he => (hg e he).comp hφ.tendsto_atTop)
    (modulus ∘ φ) (r ∘ φ) (q ∘ φ) (a ∘ φ)
    (hφ.tendsto_atTop.eventually hm) (hφ.tendsto_atTop.eventually hq)
    (hφ.tendsto_atTop.eventually hs) (hφ.tendsto_atTop.eventually hW) (hφ.tendsto_atTop.eventually hr)
    (hratio.comp hφ.tendsto_atTop) (fun k => Q (φ k)) (fun k => pN (φ k))
    (fun k => hpN (φ k)) (fun k z y => hlogN (φ k) z y)

theorem native_finite_real_original_fraction_cofinal {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (index : ℕ → ι)
    (W : ℕ → ℕ) (hWcofinal : Tendsto W atTop atTop)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun k => Z k/(Scale k)^e) atTop atTop)
    (modulus r : ℕ → ℕ) (hm : ∀ᶠ k in atTop, 0 < modulus k)
    (hs : ∀ᶠ k in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus k → prime ≤ W k)
    (hW : ∀ᶠ k in atTop, primorial (W k) ∣ modulus k)
    (hr : ∀ᶠ k in atTop, (primorial (W k)).Coprime (r k))
    (hratio : Tendsto (fun k => Scale k/(modulus k : ℝ)) atTop atTop)
    (Q : ∀ k, (Option (Fin n) → ℝ) → (D (index k)).G)
    (p : ∀ k, RoughVectorMvPolynomial (Option (Fin n)) (D (index k)).E)
    (hp : ∀ k, RoughVectorMvDegreeLE (p k) d)
    (hlog : ∀ k (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (p k) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := (D (index k)).E) (I := (D (index k)).I)
        (Q k (Option.elim · z y))) :
    Tendsto (fun k =>
      (((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).filter
        (fun t => RoughNativeRealComplexLargeIndex (D (index k)) (Q k) t t (Z k) c C L B η)).card : ℝ)/
      ((roughDyadicResidueSteps (Scale k) (modulus k) (r k)).card : ℝ)) atTop (𝓝 0) := by
  apply native_finite_real_residual_fraction_cofinal D index W hWcofinal n d c C B η L
    hc hC hB hη Scale Z hScale hg modulus r (fun _ => 1) (fun _ _ => 0)
    hm (Eventually.of_forall (fun _ => Nat.zero_lt_one)) hs hW hr hratio Q p hp
  intro k z y
  rw [rough_native_residual_identity_source]
  exact hlog k z y

end Hindman168
