import Hindman168.NativeSequentialDescentStep

/-! Genuine well-founded sequential descent, without a factorization or
irrationality oracle. Each failure gives the actual smaller rational
filtration and corrected source. Termination yields ONE fixed filtration
with ALL rational level-character limits. All-real identities retain a
finite chronological left product and reversed right product of original
rational binomial factors; no unbounded rational conjugation is introduced. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_finite_descent {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (hpos : ∀ n, 0 < L n)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hz : ∀ n, roughVectorMvEval (p n) (fun _ => (0 : ℝ)) = 0) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∃ H : NativeRationalSubgroupFiltration D ℓ,
      ∃ q : ℕ → RoughVectorMvPolynomial Unit D.E,
      ∃ as : List (NativeSequentialBinomialFactor D),
        (∀ k, H.layer k ≤ F.layer k) ∧
        as.length + nativeRationalSubgroupFiltrationDimension D H ≤ nativeRationalSubgroupFiltrationDimension D F ∧
        (∀ n, RoughVectorMvWeightedDegree H.layer (q n) 0 ∧ roughVectorMvEval (q n) (fun _ => (0 : ℝ)) = 0) ∧
        NativeSubgroupSequentialIrrational D H (L ∘ f) q ∧
        (∀ a ∈ as, NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ f) a) ∧
        ∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            nativeSequentialFactorsLeft D n b as *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) * nativeSequentialFactorsRight D n b as := by
  classical
  induction F using (measure (nativeRationalSubgroupFiltrationDimension D)).wf.induction generalizing L p with
  | h F ih =>
      by_cases hgood : NativeSubgroupSequentialIrrational D F L p
      · refine ⟨id,strictMono_id,?_,F,p,[],fun _ => le_rfl,?_,fun n => ⟨hp n,hz n⟩,hgood,?_,?_⟩
        · exact hL
        · simp only [List.length_nil, zero_add]
          exact le_rfl
        · intro a ha
          exact False.elim (List.not_mem_nil ha)
        · intro n b
          simp only [nativeSequentialFactorsLeft, nativeSequentialFactorsRight, one_mul, mul_one]
          rfl
      · obtain ⟨f1,hf1,hL1,F1,p1,a1,hdim1,hle1,hadm1,hsource1⟩ :=
          native_sequential_irrationality_failure_descent D F L hL hpos p hp hz hgood
        obtain ⟨f2,hf2,hL2,H,q,as,hle2,hlen,hsource2,hirr,hadm2,hidentity2⟩ :=
          ih F1 hdim1 (L ∘ f1) hL1 (fun n => hpos (f1 n)) p1
            (fun n => (hsource1 n).1) (fun n => (hsource1 n).2.1)
        let a := nativeSequentialFactorReindex D a1 f2
        refine ⟨f1 ∘ f2,hf1.comp hf2,hL2,H,q,a :: as,?_,?_,hsource2,hirr,?_,?_⟩
        · intro k
          exact (hle2 k).trans (hle1 k)
        · simp only [List.length_cons]
          omega
        · intro c hc
          rcases List.mem_cons.mp hc with hc | hc
          · subst c
            exact native_sequential_factor_reindex_admissible D ℓ (L ∘ f1) a1 hadm1 f2
          · exact hadm2 c hc
        · intro n b
          have hfirst := (hsource1 (f2 n)).2.2 b
          have hsecond := hidentity2 n b
          have hreplace := congrArg (fun g : D.G => nativeSequentialFactorLeft D a1 (f2 n) b * g *
            nativeSequentialFactorRight D a1 (f2 n) b) hsecond
          apply hfirst.trans (hreplace.trans _)
          change nativeSequentialFactorLeft D a1 (f2 n) b *
            (nativeSequentialFactorsLeft D n b as *
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) * nativeSequentialFactorsRight D n b as) *
            nativeSequentialFactorRight D a1 (f2 n) b =
            (nativeSequentialFactorLeft D a1 (f2 n) b * nativeSequentialFactorsLeft D n b as) *
              nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
                (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) *
              (nativeSequentialFactorsRight D n b as * nativeSequentialFactorRight D a1 (f2 n) b)
          group

end Hindman168
