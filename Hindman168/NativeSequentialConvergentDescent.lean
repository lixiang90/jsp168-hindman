import Hindman168.NativeSequentialScaledLimits

/-! Complete actual finite sequential descent with ONE subsequence for
every bounded scaled correction coefficient. Exact original all-real group
factorization and simultaneous ALL rational level-character limits are
retained. Smooth function convergence and rational periodicity still need
their separate analytic/algebraic proofs. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_convergent_descent {s ℓ : ℕ}
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
        (∀ a ∈ as, NativeSequentialBinomialFactorAdmissible D ℓ (L ∘ f) a ∧
          ∃ c : ℝ, Tendsto (fun n => (L (f n))^a.order * a.realCoefficient n) atTop (𝓝 c)) ∧
        ∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            nativeSequentialFactorsLeft D n b as *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) * nativeSequentialFactorsRight D n b as := by
  obtain ⟨f1,hf1,hL1,H,q,as,hle,hlen,hsource,hirr,hadm,hidentity⟩ :=
    native_sequential_finite_descent D F L hL hpos p hp hz
  obtain ⟨f2,hf2,hlim⟩ := native_sequential_scaled_coefficients_joint_limits D ℓ (L ∘ f1)
    (fun n => hpos (f1 n)) as hadm
  refine ⟨f1 ∘ f2,hf1.comp hf2,hL1.comp hf2.tendsto_atTop,H,q ∘ f2,
    as.map (fun a => nativeSequentialFactorReindex D a f2),hle,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_map] using hlen
  · intro n
    exact hsource (f2 n)
  · exact native_subgroup_sequential_irrational_subsequence D H (L ∘ f1) q hirr f2 hf2
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact ⟨native_sequential_factor_reindex_admissible D ℓ (L ∘ f1) b (hadm b hb) f2,
      hlim b hb⟩
  · intro n b
    have hProducts := congrArg₂ (fun a c : D.G => a * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (q (f2 n)) (fun _ => b)) * c)
      (native_sequential_factors_left_reindex D as f2 n b)
      (native_sequential_factors_right_reindex D as f2 n b)
    exact (hidentity (f2 n) b).trans hProducts.symm

end Hindman168
