import Hindman168.NativeRightCosetPeriod

/-! Complete sequential smooth/irrational/periodic factorization, using
ONE actual subsequence and the ORIGINAL group, lattice and filtration.
All-real group identities remain exact; the fixed rational residue pattern
is asserted only at signed integer inputs in the actual lattice quotient. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSequentialPeriodicFactorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E) : Prop :=
    ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∃ H : NativeRationalSubgroupFiltration D ℓ,
      ∃ q : ℕ → RoughVectorMvPolynomial Unit D.E,
      ∃ as : List (NativeSequentialBinomialFactor D),
      ∃ c gamma : ℕ → D.G, ∃ cLimit : D.G, ∃ K : Set D.G,
        (∀ k, H.layer k ≤ F.layer k) ∧
        as.length + nativeRationalSubgroupFiltrationDimension D H ≤ nativeRationalSubgroupFiltrationDimension D F ∧
        (∀ n, RoughVectorMvWeightedDegree H.layer (q n) 0 ∧ roughVectorMvEval (q n) (fun _ => (0 : ℝ)) = 0) ∧
        NativeSubgroupSequentialIrrational D H (L ∘ f) q ∧
        (∀ a ∈ as, NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ f) a ∧
          ∃ z : ℝ, Tendsto (fun n => (L (f n))^a.order * a.realCoefficient n) atTop (𝓝 z)) ∧
        (IsCompact K ∧ cLimit ∈ K ∧ ∀ n, c n ∈ K) ∧
        Tendsto c atTop (𝓝 cLimit) ∧
        (NativeSequentialSmoothCurveLimit D (L ∘ f) c as ∧ NativeSequentialBodyVelocityLimit D (L ∘ f) c as) ∧
        (∀ n, gamma n ∈ D.Γ) ∧
        (∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            (c n * nativeSequentialFactorsLeft D n b as) *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) *
            nativeSequentialFactorsRight D n b as * gamma n) ∧
        ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → D.G,
          (∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) ∧
          ∀ n : ℕ, ∀ b : ℤ, (nativeSequentialFactorsRight D n (b : ℝ) as : D.G ⧸ D.Γ) =
            (sigma (signedPeriodResidue M hM b) : D.G ⧸ D.Γ)

theorem native_sequential_adapted_periodic_factorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    NativeSequentialPeriodicFactorization D F L p := by
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hcoeff,hcompact,hc,_,hgamma,hidentity⟩ :=
    native_sequential_adapted_intrinsic_factorization D F L hL p hp
  obtain ⟨M,hM,g,hg,sigma,hRat,hPattern⟩ := native_right_original_frozen_residue_pattern D as
    (fun a ha => (hcoeff a ha).1.2.2.1)
  let bs := as.map (fun a => nativeSequentialFactorReindex D a g)
  have hLength : Tendsto (L ∘ (f ∘ g)) atTop atTop := hLf.comp hg.tendsto_atTop
  have hConstant : Tendsto (c ∘ g) atTop (𝓝 cLimit) := hc.comp hg.tendsto_atTop
  have hCoeffs : ∀ a ∈ bs, NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ (f ∘ g)) a ∧
      ∃ z : ℝ, Tendsto (fun n => (L (f (g n)))^a.order * a.realCoefficient n) atTop (𝓝 z) := by
    intro x hx
    obtain ⟨a,ha,he⟩ := List.mem_map.mp (show x ∈ as.map (fun a => nativeSequentialFactorReindex D a g) from hx)
    subst x
    obtain ⟨haAd,z,hz⟩ := hcoeff a ha
    exact ⟨native_sequential_factor_reindex_admissible D ℓ (L ∘ f) a haAd g,
      z,hz.comp hg.tendsto_atTop⟩
  refine ⟨f ∘ g,hf.comp hg,hLength,H,q ∘ g,bs,c ∘ g,gamma ∘ g,cLimit,K,hle,?_,
    (fun n => hsource (g n)),?_,hCoeffs,?_,hConstant,?_,(fun n => hgamma (g n)),?_,M,hM,sigma,hRat,?_⟩
  · simpa only [bs,List.length_map] using hlen
  · exact native_subgroup_sequential_irrational_subsequence D H (L ∘ f) q hirr g hg
  · exact ⟨hcompact.1,hcompact.2.1,fun n => hcompact.2.2 (g n)⟩
  · exact ⟨native_sequential_smooth_curve_limits D _ hLength _ cLimit hConstant bs
      (fun a ha => (hCoeffs a ha).2),
      native_sequential_body_velocity_limits D _ hLength _ cLimit hConstant bs
      (fun a ha => (hCoeffs a ha).2)⟩
  · intro n b
    simpa only [Function.comp_apply,bs,native_sequential_factors_left_reindex,
      native_sequential_factors_right_reindex] using hidentity (g n) b
  · intro n b
    rw [show nativeSequentialFactorsRight D n (b : ℝ) bs =
      nativeSequentialFactorsRight D (g n) (b : ℝ) as from native_sequential_factors_right_reindex D as g n _]
    exact hPattern n b

theorem native_original_linear_sequence_periodic_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (g a : ℕ → D.G) :
    NativeSequentialPeriodicFactorization D (nativeOriginalSubgroupLieFiltration D) L
      (fun n => nativeOriginalLeftLinearLog D (g n) (a n)) :=
  native_sequential_adapted_periodic_factorization D (nativeOriginalSubgroupLieFiltration D) L hL _
    (fun n => native_original_left_linear_log_weighted D (g n) (a n))

theorem native_factorization_original_quotient_identity {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (x h q r sigma gamma : D.G)
    (hidentity : x = h * q * r * gamma) (hgamma : gamma ∈ D.Γ)
    (hr : (r : D.G ⧸ D.Γ) = (sigma : D.G ⧸ D.Γ)) :
    (x : D.G ⧸ D.Γ) = (h * q * sigma : D.G ⧸ D.Γ) := by
  subst x
  apply QuotientGroup.eq.mpr
  have hmem : r⁻¹ * sigma ∈ D.Γ := QuotientGroup.eq.mp hr
  have hprod := D.Γ.mul_mem (D.Γ.inv_mem hgamma) hmem
  simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hprod

end Hindman168
