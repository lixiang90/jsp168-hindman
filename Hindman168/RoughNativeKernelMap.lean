import Hindman168.RoughNativeKernelNilmanifold
import Hindman168.RoughNativeKernelLogPolynomial
import Hindman168.RoughNativeNilmanifoldLogTransfer

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

variable {σ : Type*} {s : ℕ} (D : NativeNilmanifoldData.{u} s)
  (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
  (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
  (χ : D.E →ₗ[ℝ] ℝ)
  (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
    χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
  (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
    ∃ r : ℚ, χ x = (r : ℝ))
  (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
  (j : ℤ) (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
  (a m : MvPolynomial σ ℝ) (P : (σ → ℝ) → D.G)
  (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
  (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
    MvPolynomial.eval x a + MvPolynomial.eval x m)

noncomputable def roughNativeKernelMap :
    (σ → ℝ) → (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr j).G :=
  fun x => ⟨roughNativeKernelFactor (I := D.I) V
    (MvPolynomial.eval x a) (MvPolynomial.eval x m) (P x),
    rough_native_kernel_factor_mem S χ hχ V hVS hχV _ _ (P x) (hP x) (hchar x)⟩

theorem roughNativeKernelMap_val (x : σ → ℝ) :
    (roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hchar x).val =
      roughNativeKernelFactor (I := D.I) V (MvPolynomial.eval x a) (MvPolynomial.eval x m) (P x) := rfl

theorem roughNativeKernelMap_log_polynomial
    (p : RoughVectorMvPolynomial σ D.E)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
    (d : ℕ) (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d) (hd : RoughVectorMvDegreeLE p d) :
    let N := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr j
    ∃ q : RoughVectorMvPolynomial σ N.E,
      RoughVectorMvDegreeLE q
        ((((Group.nilpotencyClass D.G * Group.nilpotencyClass D.G + 1) ^
          (Group.nilpotencyClass D.G + 1)) ^ 2) * d) ∧
      ∀ x, roughVectorMvEval q x = nativeLieGlobalLogarithm (E := N.E) (I := N.I)
        (roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hchar x) := by
  intro N
  let T := nativeLieCharacterKernel S χ hχ
  let b := roughNativeKernelLogPolynomial (I := D.I) (G := D.G) V a m p
  refine ⟨roughNativeSubgroupLogPolynomial T b,
    roughNativeSubgroupLogPolynomial_degree T
      (roughNativeKernelLogPolynomial_degree V a m ha hm hd), ?_⟩
  exact roughNativeSubgroupLogPolynomial_eval T b
    (roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hchar)
    (fun x => roughNativeKernelLogPolynomial_eval V a m p P hp x)

end Hindman168
