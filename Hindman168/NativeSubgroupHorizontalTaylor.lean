import Hindman168.NativeSubgroupHorizontalLevelBridge
import Hindman168.NativeLieRationalPairIdealBCH
import Hindman168.ScalarPolynomialBinomialExpansion

/-! Horizontal scalarization commutes with the actual ordered Taylor
elimination inside a proper subgroup. No ambient horizontal assumption is
made: the kernel is a relative ideal in the initial subgroup only. -/
namespace Hindman168
open Polynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_horizontal_product {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    {v w : D.E} (hv : v ∈ F.layer 0) (hw : w ∈ F.layer 0) :
    phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w)) = phi v + phi w := by
  let V := (F.layer 0).restrictScalars ℚ
  let N := (F.layer 0 ⊓ phi.ker).restrictScalars ℚ
  have hb (a : D.E) (ha : a ∈ V) (b : D.E) (hb : b ∈ V) :
      nativeLieAdjointDifferential (I := D.I) (G := D.G) a b ∈ N :=
    ⟨F.bracket 0 0 a b ha hb, hB a ha b hb⟩
  have he := nativeLieGlobalLogarithm_product_pair_ideal (E := D.E) (I := D.I) (G := D.G)
    V N (fun _ hx => hx.1) (fun a ha b hb' => hb a ha b hb'.1) hv hw (hb v hv w hw)
  have hz := he.2
  change phi (_ - (v+w)) = 0 at hz
  rw [map_sub, map_add] at hz
  exact sub_eq_zero.mp hz

theorem native_actual_subgroup_horizontal_extension_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (chi : (nativeRationalLayerOrbitData D F 0 rho hRat).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalLayerOrbitData D F 0 rho hRat).I)
      (nativeRationalLayerOrbitData D F 0 rho hRat).Γ chi) :
    ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      nativeSubgroupHorizontalExtension D F rho hRat chi
        (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0 := by
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  intro v hv w hw
  let x : A.E := ⟨v,hv⟩
  let y : A.E := ⟨w,hw⟩
  let z : F.layer 0 := nativeLieAdjointDifferential (I := A.I) (G := A.G) x y
  have hz : chi z = 0 := hChi.2.1 (native_rational_lie_bracket_mem_commutator A x y)
  have he : (z : D.E) = nativeLieAdjointDifferential (I := D.I) (G := D.G) v w :=
    native_subgroup_differential_bracket_original D (nativeRationalSubgroupLayerAlgebra D F 0) x y
  rw [← he]
  exact (native_subgroup_horizontal_extension_agrees D F rho hRat chi z).trans hz

theorem adapted_taylor_binomial_scalar (j : ℕ) :
    scalarUnitPolynomial (adaptedTaylorBinomial j) = scalarBinomialPolynomial j := by
  apply Polynomial.funext
  intro x
  rw [scalar_unit_polynomial_eval]
  simp only [adaptedTaylorBinomial, scalarBinomialPolynomial, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, map_prod, map_sub, MvPolynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_prod_range]

theorem native_subgroup_horizontal_taylor_removal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) (k : ℕ) :
    scalarUnitPolynomial (roughVectorMvProjection phi (adaptedTaylorRemoval D p k)) =
      scalarUnitPolynomial (roughVectorMvProjection phi p) -
        Polynomial.C (phi (roughVectorMvEval p (fun _ => (k : ℝ)))) * scalarBinomialPolynomial k := by
  apply Polynomial.funext
  intro x
  rw [scalar_unit_polynomial_eval, roughVectorMvProjection_eval, adapted_taylor_removal_eval]
  rw [native_subgroup_horizontal_product D F phi hB
    ((F.layer 0).smul_mem _ (rough_vector_weighted_eval F.layer F.antitone hp _))
    (rough_vector_weighted_eval F.layer F.antitone hp _)]
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    scalar_unit_polynomial_eval, roughVectorMvProjection_eval,
    ← adapted_taylor_binomial_scalar, scalar_unit_polynomial_eval, map_smul]
  simp only [smul_eq_mul]
  ring

theorem native_subgroup_horizontal_projection_degree {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (phi : D.E →ₗ[ℝ] ℝ) (j : ℕ) (hNext : F.layer (j+1) ≤ phi.ker)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    (scalarUnitPolynomial (roughVectorMvProjection phi p)).natDegree ≤ j := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [scalar_unit_polynomial_coefficient, ← rough_vector_coefficient_projection]
  apply hNext
  have hm := rough_vector_weighted_coefficient F.layer F.antitone hp (Finsupp.single () k)
  simp only [Finsupp.sum_single_index, Nat.add_zero] at hm
  exact F.antitone (by omega) hm

end Hindman168
