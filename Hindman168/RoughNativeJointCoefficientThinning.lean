import Hindman168.RoughJointCoefficientThinning
import Hindman168.RoughJointScalarReparametrization
import Hindman168.RoughJointProgressionPolynomial
import Hindman168.NativeNilmanifoldData

namespace Hindman168
open scoped Classical Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

/-- Fractional-part thinning preserves the actual native joint map, all
positive-degree models, weighted degrees, and the specified subgroup. -/
theorem rough_native_joint_coefficient_thinning {κ : Type*} [Fintype κ] {step : ℕ}
    (D : NativeNilmanifoldData.{u} step) (support : Finset (κ →₀ ℕ))
    (q H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀ (w : ℕ) (Z A : ℝ)
      (P0 : Polynomial ℝ) (theta : (κ →₀ ℕ) → Polynomial ℝ)
      (M : (κ →₀ ℕ) → Polynomial ℚ) (S : Subgroup D.G) (ξ : D.G → ℝ)
      (P : (Option κ → ℝ) → D.G), N ≤ w → P0.natDegree ≤ q →
      (∀ J ∈ support, (theta J).natDegree+J.sum (fun _ e => e) ≤ q) →
      (∀ J ∈ support, RoughCoefficientModel w N q (∑ j, J j) Z A (theta J) (M J)) →
      (∀ x, P x ∈ S) →
      (∀ x, ξ (P x) = MvPolynomial.eval x (roughSpatialJointPolynomial support P0 theta)) →
      ∀ (pLog : RoughVectorMvPolynomial (Option κ) D.E),
      (∀ x, roughVectorMvEval pLog x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x)) →
      RoughVectorMvDegreeLE pLog q →
      ∃ (a b : ℕ) (M0 : Polynomial ℚ) (Q : (Option κ → ℝ) → D.G)
        (pNew : RoughVectorMvPolynomial (Option κ) D.E),
        let P0new := P0.comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X)
        let θnew := fun J => (theta J).comp (Polynomial.C (a : ℝ)+Polynomial.C (b : ℝ)*Polynomial.X)
        let Mnew := fun J => (M J).comp (Polynomial.C (a : ℚ)+Polynomial.C (b : ℚ)*Polynomial.X)
        0 < b ∧ b ≤ N ∧ (∀ z : ℕ, z < H → a+b*z < N) ∧
        M0.natDegree ≤ q ∧ (∀ j prime, prime.Prime → prime ∣ (M0.coeff j).den → prime ≤ w) ∧
        (∀ z : ℕ, z < H → (∃ n : ℤ, M0.eval (z : ℚ) = (n : ℚ)) ∧
          0 ≤ P0new.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
          P0new.eval (z : ℝ)-((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) ∧
        (∀ J ∈ support, RoughCoefficientModel w H q (∑ j, J j) Z A (θnew J) (Mnew J)) ∧
        P0new.natDegree ≤ q ∧
        (∀ J ∈ support, (θnew J).natDegree+J.sum (fun _ e => e) ≤ q) ∧
        (∀ x, Q x = P (Option.elim · ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j)))) ∧
        (∀ x, Q x ∈ S) ∧
        (∀ x, ξ (Q x) = MvPolynomial.eval x (roughSpatialJointPolynomial support P0new θnew)) ∧
        RoughVectorMvDegreeLE pNew q ∧
        ∀ x, roughVectorMvEval pNew x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q x) := by
  obtain ⟨N, hN, hthin⟩ := rough_joint_coefficient_thinning support q H hH
  refine ⟨N, hN, ?_⟩
  intro w Z A P0 theta M S ξ P hNw hP0 htheta hmodels hmem hchar pLog hpLog hdegree
  obtain ⟨a, b, M0, hb, hbN, hindex, hM0, hden, hval, hmodels'⟩ :=
    hthin w q (fun J => ∑ j, J j) Z A theta M P0 hNw hP0 hmodels
  let Q : (Option κ → ℝ) → D.G := fun x =>
    P (Option.elim · ((a : ℝ)+(b : ℝ)*x none) (fun j => x (some j)))
  obtain ⟨pNew, hnewdeg, hnewlog⟩ := rough_joint_progression_polynomial
    (nativeLieGlobalLogarithm (E := D.E) (I := D.I)) P pLog q hdegree
    (fun z y => hpLog (Option.elim · z y)) (a : ℝ) (b : ℝ)
  have hcoords : ∀ x : Option κ → ℝ, (Option.elim · (x none) (fun j => x (some j))) = x := by
    intro x
    funext j
    cases j <;> rfl
  have hdeg := rough_joint_scalar_reparametrized_degree support P0 theta q hP0 htheta (a : ℝ) (b : ℝ)
  refine ⟨a, b, M0, Q, pNew, hb, hbN, hindex, hM0, hden, ?_, hmodels', hdeg.1,
    hdeg.2.1, fun _ => rfl, fun x => hmem _, ?_, hnewdeg, ?_⟩
  · intro z hz
    obtain ⟨he, hlo, hhi⟩ := hval z hz
    refine ⟨⟨⌊P0.eval ((a+b*z : ℕ) : ℝ)⌋, he⟩, ?_⟩
    simpa only [rough_affine_comp_eval] using And.intro hlo hhi
  · intro x
    rw [show ξ (Q x) = ξ (P (Option.elim · ((a : ℝ)+(b : ℝ)*x none)
      (fun j => x (some j)))) from rfl, hchar]
    have he := rough_joint_scalar_reparametrization support P0 theta (a : ℝ) (b : ℝ)
      (x none) (fun j => x (some j))
    rw [hcoords x] at he
    exact he.symm
  · intro x
    have he := hnewlog (x none) (fun j => x (some j))
    rw [hcoords x] at he
    exact he

end Hindman168
