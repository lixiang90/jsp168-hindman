import Hindman168.RoughNativeDescentPolynomial
import Hindman168.RoughFiniteCoefficientAssembly

namespace Hindman168
open MvPolynomial
open scoped Manifold ContDiff BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_model_descent_polynomial {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
    (support : Finset (κ →₀ ℕ)) {w H q : ℕ} {Z A : ℝ}
    (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
    (M0 : Polynomial ℚ) (M : (κ →₀ ℕ) → Polynomial ℚ)
    (hmodels : ∀ J ∈ support, RoughCoefficientModel w H q (∑ k, J k) Z A (theta J) (M J))
    (hM0 : M0.natDegree ≤ q) (he : ∀ J ∈ support, (∑ k, J k) ≤ q)
    (hP0 : P0.natDegree ≤ q)
    (htheta : ∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q)
    (P : (Option κ → ℝ) → D.G) (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
    (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
      eval x (roughSpatialJointPolynomial support P0 theta))
    (p : RoughVectorMvPolynomial (Option κ) D.E)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
    (hd : RoughVectorMvDegreeLE p q) (u : κ → ℝ) (K : ℝ) :
    let N := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr j
    let m := map (Rat.castHom ℝ) (roughSpatialJointPolynomial support M0 M)
    let a := roughSpatialJointPolynomial support P0 theta-m
    ∃ Q : (Option κ → ℝ) → N.G,
      (∀ x, (Q x).val = roughNativeKernelFactor (I := D.I) V (eval x a) (eval x m) (P x)) ∧
      Module.finrank ℝ N.E < Module.finrank ℝ D.E ∧
      ∃ b : RoughVectorMvPolynomial (Option κ) N.E,
        RoughVectorMvDegreeLE b (roughKernelDegreeFactor step*q) ∧
        ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval b (Option.elim · z y) =
          nativeLieGlobalLogarithm (E := N.E) (I := N.I)
            (Q (Option.elim · z (fun k => u k+K*y k))) := by
  intro N m a
  have hm : m.totalDegree ≤ q := rough_models_joint_real_degree support theta M0 M hmodels hM0 he
  have hn : (-m).totalDegree ≤ q := by simpa only [totalDegree_neg] using hm
  have ha : a.totalDegree ≤ q := by
    dsimp only [a]
    rw [sub_eq_add_neg]
    exact (totalDegree_add _ _).trans
      (max_le (roughSpatialJointPolynomial_degree support P0 theta q hP0 htheta) hn)
  have hc : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) = eval x a+eval x m := by
    intro x
    rw [hchar x]
    change eval x (roughSpatialJointPolynomial support P0 theta) =
      eval x (roughSpatialJointPolynomial support P0 theta-m)+eval x m
    rw [map_sub, sub_add_cancel]
  obtain ⟨hfin, b, hb, hbe⟩ := rough_native_descent_polynomial D S hS χ hχ hQ V hVr j
    hVS hχV a m P hP hc p hp q ha hm hd u K
  exact ⟨roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hc,
    fun _ => rfl, hfin, b, hb, hbe⟩

end Hindman168
