import Hindman168.NativeSequentialSmoothFactorization
import Hindman168.NativeSequentialBodyVelocityLimits

/-! Smooth sequential factorization in the ACTUAL original group topology
and native manifold body velocities, on the SAME original subsequence,
final rational filtration and actual factor list. The original step is
unchanged. Uniform rational period and local cube-Haar laws remain open. -/
namespace Hindman168
open Filter Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeSequentialIntrinsicFactorization {s ℓ : ℕ}
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
        Tendsto c atTop (𝓝 cLimit) ∧ (NativeSequentialSmoothCurveLimit D (L ∘ f) c as ∧ NativeSequentialBodyVelocityLimit D (L ∘ f) c as) ∧
        (∀ n, gamma n ∈ D.Γ) ∧
        ∀ n, ∀ b : ℝ, nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)) =
            (c n * nativeSequentialFactorsLeft D n b as) *
            nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (q n) (fun _ => b)) *
            nativeSequentialFactorsRight D n b as * gamma n

theorem native_sequential_adapted_intrinsic_factorization {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    NativeSequentialIntrinsicFactorization D F L p := by
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hcoeff,hcompact,hc,hcoord,hgamma,hidentity⟩ :=
    native_sequential_adapted_smooth_factorization D F L hL p hp
  have hbody := native_sequential_body_velocity_limits D (L ∘ f) hLf c cLimit hc as
    (fun a ha => (hcoeff a ha).2)
  exact ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,hlen,hsource,hirr,hcoeff,hcompact,hc,⟨hcoord,hbody⟩,hgamma,hidentity⟩

theorem native_original_linear_sequence_intrinsic_factorization {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (g a : ℕ → D.G) :
    NativeSequentialIntrinsicFactorization D (nativeOriginalSubgroupLieFiltration D) L
      (fun n => nativeOriginalLeftLinearLog D (g n) (a n)) :=
  native_sequential_adapted_intrinsic_factorization D (nativeOriginalSubgroupLieFiltration D) L hL _
    (fun n => native_original_left_linear_log_weighted D (g n) (a n))

end Hindman168
