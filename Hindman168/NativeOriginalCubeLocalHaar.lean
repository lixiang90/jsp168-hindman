import Hindman168.NativeResidueCubeSmoothLocalHaar
import Hindman168.NativeSequentialPeriodicFactorization
import Hindman168.CubeSignedPeriodResidue

/-! The original source cube law: exact periodic cosets, actual smooth factors,
one length threshold for all dimensions through ORIGINAL s+1 and all residues. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

def NativeCubeLocalHaarLaw {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) : Prop :=
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  ∀ beta ε : ℝ, 0 < ε → ∃ radius : ℝ, 0 < radius ∧
    ∀ t : ℕ, 0 < t → (M : ℤ) ∣ (t : ℤ) → ∀ c R : ℝ, 0 < c → 0 ≤ R →
      ∀ᶠ m in atTop, ∀ q : Fin (s+2), ∀ lo hi v : Fin (q.val+1) → ℤ,
        (∀ i : Fin q.val, (M : ℤ) ∣ v i.succ) →
        (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
        (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
        (∀ x ∈ alignmentBoxClass lo hi v t, ∀ V : Finset (Fin q.val),
          |((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ)/L m-beta| < radius) →
        ∀ f ∈ unitLipschitzObservables (Finset (Fin q.val) → D.G ⧸ D.Γ),
          ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
            (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) -
            ∫ y, f y ∂nativeResidueCubeHaarImage D H
              (sigma (signedPeriodResidue M hM (v 0))) (hRat _)
              q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)‖ < ε

theorem native_original_cube_local_haar {s ℓ : ℕ}
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
      NativeCubeLocalHaarLaw D H L P M hM sigma hRat h := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨h,hh,hlocal⟩ := native_residue_cube_smooth_local_haar D H L hL q hq hIrr c cLimit hc as hCoeffs
  refine ⟨h,hh,?_⟩
  intro beta ε hε
  obtain ⟨radius,hr,hwin⟩ := hlocal beta ε hε
  refine ⟨radius,hr,?_⟩
  intro t ht hMt a R ha hR
  have hall := Filter.eventually_all.mpr (fun d : Fin (s+2) =>
    Filter.eventually_all.mpr (fun r : Fin M =>
      hwin d.val (2^d.val-1) (nativeCubeVertexEnumeration d.val) (sigma r) (hRat r) t ht a R ha hR))
  filter_upwards [hall] with m hm
  intro d lo hi v hv hlen hloc hlocal' f hf
  have hloc' : ∀ x ∈ alignmentBoxClass lo hi v t, ∀ V : Finset (Fin d.val),
      |((x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))/L m-beta| < radius := by
    intro x hx V
    simpa only [Int.cast_add, Int.cast_sum] using hlocal' x hx V
  have hb := hm d (signedPeriodResidue M hM (v 0)) lo hi v hlen hloc hloc' f hf
  have he : ∀ x ∈ alignmentBoxClass lo hi v t, ∀ V : Finset (Fin d.val),
      (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ) =
      (c m * nativeSequentialFactorsLeft D m ((x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ)) as) •
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (q m) (fun _ => (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))) *
          sigma (signedPeriodResidue M hM (v 0)) : D.G ⧸ D.Γ) := by
    intro x hx V
    have hp := hPattern m (x 0 + ∑ i ∈ V, x i.succ)
    rw [cube_signed_period_residue hM lo hi v t hMt hv x hx V] at hp
    have hid := native_factorization_original_quotient_identity D _ _ _ _ _ _
      (hidentity m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ)) (hgamma m) hp
    simpa only [Int.cast_add, Int.cast_sum, MulAction.Quotient.smul_coe, smul_eq_mul, mul_assoc] using hid
  have hmean : finiteComplexSetMean (alignmentBoxClass lo hi v t)
      (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) =
      finiteComplexSetMean (alignmentBoxClass lo hi v t) (fun x => f (fun V =>
        (c m * nativeSequentialFactorsLeft D m ((x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ)) as) •
        (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (q m) (fun _ => (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))) *
          sigma (signedPeriodResidue M hM (v 0)) : D.G ⧸ D.Γ))) := by
    unfold finiteComplexSetMean
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    exact congrArg f (funext (he x hx))
  rw [hmean]
  exact hb

end Hindman168
