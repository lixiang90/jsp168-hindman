import Hindman168.NativeRealResidualRoughProportion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Uniform comparison on bounded normalized-scale ranges. Actual dyadic
retained factors give a FIXED range ratio, independent of the sampled tuple,
source coefficients and nilsequence complexity. -/
namespace Hindman168
open Filter
open scoped BigOperators Classical
universe u

theorem rough_real_residual_event_scale_compare {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (a : κ → ℤ) (q z t : ℕ) (Zactual Zref c C K : ℝ) (L : NNReal) (B η : ℝ)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hlo : Zref ≤ Zactual) (hhi : Zactual ≤ K*Zref)
    (h : RoughNativeRealResidualComplexLargeIndex D Q a q z t Zactual c C L B η) :
    RoughNativeRealResidualComplexLargeIndex D Q a q z t Zref c (C*K) L B η := by
  obtain ⟨lo,hi,b,F,hL,hB,hgeom,hcompatible,hlarge⟩ := h
  have hclo : c*Zref ≤ c*Zactual := mul_le_mul_of_nonneg_left hlo hc
  have hChi : C*Zactual ≤ (C*K)*Zref := by
    calc
      C*Zactual ≤ C*(K*Zref) := mul_le_mul_of_nonneg_left hhi hC
      _ = _ := by ring
  refine ⟨lo,hi,b,F,hL,hB,?_,hcompatible,hlarge⟩
  intro j
  exact ⟨hclo.trans (hgeom j).1,(hgeom j).2.1.trans hChi,
    (hgeom j).2.2.1.trans hChi,(hgeom j).2.2.2.trans hChi⟩

theorem native_real_residual_bound_variable_scale {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w R : ℕ) (Scale Zref c C K B η δ : ℝ) (L : NNReal)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (h : NativeRealResidualRoughProportionBound D n d w R Scale Zref c (C*K) B η δ L)
    (modulus r : ℕ) (hm : 0 < modulus)
    (hs : ∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w)
    (hW : primorial w ∣ modulus) (hr : (primorial w).Coprime r)
    (hratio : (R : ℝ) ≤ Scale/(modulus : ℝ))
    (q : ℕ) (a : Fin n → ℤ) (hq : 0 < q)
    (Q : (Option (Fin n) → ℝ) → D.G) (pN : RoughVectorMvPolynomial (Option (Fin n)) D.E)
    (hpN : RoughVectorMvDegreeLE pN d)
    (hlogN : ∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval pN (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (roughNativeResidualSource D Q a q (Option.elim · z y)))
    (Zactual : ℕ → ℝ)
    (hZrange : ∀ t ∈ roughDyadicResidueSteps Scale modulus r, Zref ≤ Zactual t ∧ Zactual t ≤ K*Zref) :
    (((roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t (Zactual t) c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ) := by
  have hfixed := h modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN
  have hsub : (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t (Zactual t) c C L B η) ⊆
      (roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t Zref c (C*K) L B η) := by
    intro t ht
    obtain ⟨ht,hbad⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨ht,rough_real_residual_event_scale_compare D Q a q t t
      (Zactual t) Zref c C K L B η hc hC (hZrange t ht).1 (hZrange t ht).2 hbad⟩
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hfixed

theorem rough_dyadic_retained_product_scale_range {ι : Type*} [Fintype ι]
    (S : ι → ℝ) (t : ι → ℕ) (M : ℕ) (hM : 0 < M)
    (hS : ∀ i, 0 < S i) (ht : ∀ i, S i ≤ (t i : ℝ) ∧ (t i : ℝ) ≤ 2*S i)
    (Z₀ : ℝ) (hZ₀ : 0 ≤ Z₀) :
    0 < M*(∏ i, t i) ∧
      Z₀/((2 : ℝ)^Fintype.card ι*((M : ℝ)*∏ i, S i)) ≤ Z₀/(M*(∏ i, t i) : ℕ) ∧
      Z₀/(M*(∏ i, t i) : ℕ) ≤
        (2 : ℝ)^Fintype.card ι*(Z₀/((2 : ℝ)^Fintype.card ι*((M : ℝ)*∏ i, S i))) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hprod : (0 : ℝ) < ∏ i, S i := Finset.prod_pos (fun i _ => hS i)
  have hbase : (0 : ℝ) < (M : ℝ)*∏ i, S i := mul_pos hMR hprod
  have hK : (0 : ℝ) < (2 : ℝ)^Fintype.card ι := by positivity
  have hloP : (∏ i, S i) ≤ ∏ i, (t i : ℝ) :=
    Finset.prod_le_prod (fun i _ => (hS i).le) (fun i _ => (ht i).1)
  have hhiP : (∏ i, (t i : ℝ)) ≤ (2 : ℝ)^Fintype.card ι*∏ i, S i := by
    calc
      _ ≤ ∏ i, (2 : ℝ)*S i := Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => (ht i).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ]
  have hqlo : (M : ℝ)*∏ i, S i ≤ ((M*(∏ i, t i) : ℕ) : ℝ) := by
    rw [Nat.cast_mul,Nat.cast_prod]
    exact mul_le_mul_of_nonneg_left hloP hMR.le
  have hqhi : ((M*(∏ i, t i) : ℕ) : ℝ) ≤ (2 : ℝ)^Fintype.card ι*((M : ℝ)*∏ i, S i) := by
    rw [Nat.cast_mul,Nat.cast_prod]
    calc
      _ ≤ (M : ℝ)*((2 : ℝ)^Fintype.card ι*∏ i, S i) := mul_le_mul_of_nonneg_left hhiP hMR.le
      _ = _ := by ring
  have hqR : (0 : ℝ) < (M*(∏ i, t i) : ℕ) := hbase.trans_le hqlo
  refine ⟨by exact_mod_cast hqR,div_le_div_of_nonneg_left hZ₀ hqR hqhi,?_⟩
  calc
    _ ≤ Z₀/((M : ℝ)*∏ i, S i) := div_le_div_of_nonneg_left hZ₀ hbase hqlo
    _ = _ := by field_simp

theorem native_finite_real_residual_variable_scale_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (n d : ℕ) (c C K B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 1 ≤ K) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Zref : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ e : ℝ, 0 < e → Tendsto (fun w => Zref w/(Scale w)^e) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop, ∀ i : ι,
      ∀ modulus r : ℕ, 0 < modulus →
      (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
      primorial w ∣ modulus → (primorial w).Coprime r →
      (R : ℝ) ≤ Scale w/(modulus : ℝ) →
      ∀ (q : ℕ) (a : Fin n → ℤ), 0 < q →
      ∀ (Q : (Option (Fin n) → ℝ) → (D i).G)
        (pN : RoughVectorMvPolynomial (Option (Fin n)) (D i).E),
      RoughVectorMvDegreeLE pN d →
      (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval pN (Option.elim · z y) =
        nativeLieGlobalLogarithm (E := (D i).E) (I := (D i).I)
          (roughNativeResidualSource (D i) Q a q (Option.elim · z y))) →
      ∀ Zactual : ℕ → ℝ,
      (∀ t ∈ roughDyadicResidueSteps (Scale w) modulus r,
        Zref w ≤ Zactual t ∧ Zactual t ≤ K*Zref w) →
      (((roughDyadicResidueSteps (Scale w) modulus r).filter
        (fun t => RoughNativeRealResidualComplexLargeIndex (D i) Q a q t t (Zactual t) c C L B η)).card : ℝ) <
        δ*((roughDyadicResidueSteps (Scale w) modulus r).card : ℝ) := by
  obtain ⟨R,hR,hbound⟩ := native_finite_real_residual_rough_proportion_uniform D n d c (C*K) B η L
    hc (mul_nonneg hC (zero_le_one.trans hK)) hB hη Scale Zref hScale hg hδ
  refine ⟨R,hR,hbound.mono ?_⟩
  intro w hw i modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN Zactual hZrange
  exact native_real_residual_bound_variable_scale (D i) n d w R (Scale w) (Zref w) c C K B η δ L
    hc.le hC (hw i) modulus r hm hs hW hr hratio q a hq Q pN hpN hlogN Zactual hZrange

end Hindman168
