import Hindman168.NativeCompactSequenceLimits

/-! Arbitrary original adapted sequences: genuine initial compact lattice
normalization, finite sequential descent, one final rational filtration,
ALL rational level-character limits, convergent compact constants and
simultaneously convergent scaled smooth coefficients. The exact ALL-real
group identity includes the actual original right lattice factor.
Local uniform smooth limits and a bounded rational period remain separate
unfinished parts of the paper's complete factorization lemma. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSequentialAlgebraicFactorization {s ℓ : ℕ}
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
        Tendsto c atTop (𝓝 cLimit) ∧ (∀ n, gamma n ∈ D.Γ) ∧
        ∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            (c n * nativeSequentialFactorsLeft D n b as) *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) *
            nativeSequentialFactorsRight D n b as * gamma n

theorem native_sequential_adapted_algebraic_factorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (hpos : ∀ n, 0 < L n)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    NativeSequentialAlgebraicFactorization D F L p := by
  obtain ⟨K,hK,_,c0,gamma0,p0,hnorm⟩ := native_subgroup_sequence_compact_normalization D F p hp
  obtain ⟨cLimit,hcLimit,f0,hf0,hcLim⟩ := native_compact_sequence_limit D K hK c0 (fun n => (hnorm n).1)
  obtain ⟨f1,hf1,hL1,H,q,as,hle,hlen,hsource,hirr,hadm,hidentity⟩ :=
    native_sequential_convergent_descent D F (L ∘ f0) (hL.comp hf0.tendsto_atTop)
      (fun n => hpos (f0 n)) (p0 ∘ f0)
      (fun n => (hnorm (f0 n)).2.2.1) (fun n => (hnorm (f0 n)).2.2.2.1)
  refine ⟨f0 ∘ f1,hf0.comp hf1,hL1,H,q,as,(c0 ∘ f0) ∘ f1,(gamma0 ∘ f0) ∘ f1,
    cLimit,K,hle,hlen,hsource,hirr,hadm,?_,hcLim.comp hf1.tendsto_atTop,?_,?_⟩
  · exact ⟨hK,hcLimit,fun n => (hnorm (f0 (f1 n))).1⟩
  · intro n
    exact (hnorm (f0 (f1 n))).2.1
  · intro n b
    have hfirst := (hnorm (f0 (f1 n))).2.2.2.2 b
    have hreplace := congrArg (fun g : D.G => c0 (f0 (f1 n)) * g * gamma0 (f0 (f1 n))) (hidentity n b)
    apply hfirst.trans (hreplace.trans _)
    simp only [Function.comp_def, mul_assoc]

theorem native_sequential_adapted_factorization_cofinal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    NativeSequentialAlgebraicFactorization D F L p := by
  obtain ⟨f0,hf0,hpos⟩ := extraction_of_eventually_atTop (hL.eventually_gt_atTop 0)
  obtain ⟨f1,hf1,hL1,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hadm,hcompact,hclim,hgamma,hidentity⟩ :=
    native_sequential_adapted_algebraic_factorization D F (L ∘ f0) (hL.comp hf0.tendsto_atTop)
      hpos (p ∘ f0) (fun n => hp (f0 n))
  exact ⟨f0 ∘ f1,hf0.comp hf1,hL1,H,q,as,c,gamma,cLimit,K,
    hle,hlen,hsource,hirr,hadm,hcompact,hclim,hgamma,hidentity⟩

end Hindman168
