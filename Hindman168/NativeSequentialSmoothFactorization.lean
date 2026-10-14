import Hindman168.NativeSequentialSmoothLimits
import Hindman168.NativeOriginalSequentialFactorization

/-! Unconditional actual sequential factorization with the smooth conclusion
on the SAME subsequence, final rational filtration and raw factor list.
All-character irrationality and exact original group identities are retained.
Uniform rational periodicity and subsequent cube-Haar laws remain unproved. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSequentialSmoothFactorization {s ℓ : ℕ}
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
        Tendsto c atTop (𝓝 cLimit) ∧ NativeSequentialSmoothCurveLimit D (L ∘ f) c as ∧
        (∀ n, gamma n ∈ D.Γ) ∧
        ∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            (c n * nativeSequentialFactorsLeft D n b as) *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) *
            nativeSequentialFactorsRight D n b as * gamma n

theorem native_sequential_adapted_smooth_factorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    NativeSequentialSmoothFactorization D F L p := by
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hcoeff,hcompact,hc,hgamma,hidentity⟩ :=
    native_sequential_adapted_factorization_cofinal D F L hL p hp
  have hsmooth := native_sequential_smooth_curve_limits D (L ∘ f) hLf c cLimit hc as
    (fun a ha => (hcoeff a ha).2)
  exact ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hcoeff,hcompact,hc,hsmooth,hgamma,hidentity⟩

theorem native_original_linear_sequence_smooth_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (g a : ℕ → D.G) :
    NativeSequentialSmoothFactorization D (nativeOriginalSubgroupLieFiltration D) L
      (fun n => nativeOriginalLeftLinearLog D (g n) (a n)) :=
  native_sequential_adapted_smooth_factorization D (nativeOriginalSubgroupLieFiltration D) L hL _
    (fun n => native_original_left_linear_log_weighted D (g n) (a n))

end Hindman168
