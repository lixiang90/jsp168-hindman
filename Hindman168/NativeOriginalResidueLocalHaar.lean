import Hindman168.NativeRationalLayerSmoothLocalHaar
import Hindman168.NativeSequentialPeriodicFactorization
import Hindman168.SignedProgressionResidue

/-! Local point laws for the ORIGINAL source on all fixed-period signed
progressions. Exact group factorization and actual lattice cosets are used;
no replacement source, normal-lattice assumption or Haar oracle is introduced. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeResidueLocalHaarLaw {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) : Prop :=
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta ε : ℝ, 0 < ε → ∃ radius : ℝ, 0 < radius ∧
    ∀ d : ℤ, d ≠ 0 → (M : ℤ) ∣ d → ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ᶠ n in atTop, ∀ b : ℤ, ∀ m : ℕ, τ*L n ≤ m →
        (∀ x ∈ scalarMvIntegerCube Unit m, |((b+d*x () : ℤ) : ℝ)/L n-beta| < radius) →
        ∀ f ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          ‖finiteComplexSetMean (scalarMvIntegerCube Unit m)
            (fun x => f (P n ((b+d*x () : ℤ) : ℝ) : D.G ⧸ D.Γ)) -
            ∫ y, f y ∂nativeRationalLayerHaarImage D H 0
              (sigma (signedPeriodResidue M hM b)) (hRat _) (h beta)‖ < ε

theorem native_original_residue_local_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (q : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hq : ∀ n, RoughVectorMvWeightedDegree H.layer (q n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D H L q)
    (c : ℕ → D.G) (cLimit : D.G) (hc : Tendsto c atTop (𝓝 cLimit))
    (as : List (NativeSequentialBinomialFactor D))
    (hCoeffs : ∀ a ∈ as, ∃ z : ℝ,
      Tendsto (fun n => (L n)^a.order * a.realCoefficient n) atTop (𝓝 z))
    (P : ℕ → ℝ → D.G) (gamma : ℕ → D.G) (hgamma : ∀ n, gamma n ∈ D.Γ)
    (hidentity : ∀ n t, P n t = (c n * nativeSequentialFactorsLeft D n t as) *
      nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (q n) (fun _ => t)) *
      nativeSequentialFactorsRight D n t as * gamma n)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (hPattern : ∀ n : ℕ, ∀ b : ℤ, (nativeSequentialFactorsRight D n (b : ℝ) as : D.G ⧸ D.Γ) =
      (sigma (signedPeriodResidue M hM b) : D.G ⧸ D.Γ)) :
    ∃ h : ℝ → D.G, ContMDiff 𝓘(ℝ) D.I ∞ h ∧
      NativeResidueLocalHaarLaw D H L P M hM sigma hRat h := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨h,hh,hlocal⟩ := native_rational_layer_smooth_local_haar D H L hL q hq hIrr c cLimit hc as hCoeffs
  refine ⟨h,hh,?_⟩
  intro beta ε hε
  obtain ⟨radius,hr,hwin⟩ := hlocal beta ε hε
  refine ⟨radius,hr,?_⟩
  intro d hd hdM τ hτ hτ1
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hall := Filter.eventually_all.mpr
    (fun r : Fin M => hwin (sigma r) (hRat r) (d : ℚ) hdQ τ hτ hτ1)
  filter_upwards [hall] with n hn
  intro b m hm hloc f hf
  have hloc' : ∀ x ∈ scalarMvIntegerCube Unit m,
      |((b : ℝ)+((d : ℚ) : ℝ)*(x () : ℝ))/L n-beta| < radius := by
    intro x hx
    simpa only [Int.cast_add, Int.cast_mul, Rat.cast_intCast] using hloc x hx
  have hb := hn (signedPeriodResidue M hM b) (b : ℝ) m hm hloc' f hf
  have hsource (x : Unit → ℤ) :
      (P n ((b+d*x () : ℤ) : ℝ) : D.G ⧸ D.Γ) =
        (c n * nativeSequentialFactorsLeft D n ((b : ℝ)+((d : ℚ) : ℝ)*(x () : ℝ)) as) •
          (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (q n) (fun i => (b : ℝ)+((d : ℚ) : ℝ)*(x i : ℝ))) *
              sigma (signedPeriodResidue M hM b) : D.G ⧸ D.Γ) := by
    have hp := hPattern n (b+d*x ())
    rw [signed_period_residue_progression M hM b d (x ()) hdM] at hp
    have he := native_factorization_original_quotient_identity D _ _ _ _ _ _
      (hidentity n ((b+d*x () : ℤ) : ℝ)) (hgamma n) hp
    have hi : (fun i : Unit => (b : ℝ)+((d : ℚ) : ℝ)*(x i : ℝ)) =
        (fun _ : Unit => ((b+d*x () : ℤ) : ℝ)) := by
      funext i
      cases i
      simp only [Int.cast_add, Int.cast_mul, Rat.cast_intCast]
    rw [hi, MulAction.Quotient.smul_coe, smul_eq_mul]
    simpa only [Int.cast_add, Int.cast_mul, Rat.cast_intCast, mul_assoc] using he
  have heq : (fun x : Unit → ℤ => f (P n ((b+d*x () : ℤ) : ℝ) : D.G ⧸ D.Γ)) =
      (fun x => f ((c n * nativeSequentialFactorsLeft D n ((b : ℝ)+((d : ℚ) : ℝ)*(x () : ℝ)) as) •
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (q n) (fun i => (b : ℝ)+((d : ℚ) : ℝ)*(x i : ℝ))) *
          sigma (signedPeriodResidue M hM b) : D.G ⧸ D.Γ))) := by
    funext x
    exact congrArg f (hsource x)
  rw [heq]
  exact hb

end Hindman168
