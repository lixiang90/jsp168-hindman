import Hindman168.RoughNativeKernelMap
import Hindman168.RoughSpatialSubstitution

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_kernel_spatial_log_polynomial {κ : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (j : ℤ) (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
    (a m : MvPolynomial (Option κ) ℝ) (P : (Option κ → ℝ) → D.G)
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
    (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
      MvPolynomial.eval x a + MvPolynomial.eval x m)
    (p : RoughVectorMvPolynomial (Option κ) D.E)
    (hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
    (d : ℕ) (ha : a.totalDegree ≤ d) (hm : m.totalDegree ≤ d) (hd : RoughVectorMvDegreeLE p d)
    (u : κ → ℝ) (K : ℝ) :
    let N := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr j
    ∃ q : RoughVectorMvPolynomial (Option κ) N.E,
      RoughVectorMvDegreeLE q
        ((((Group.nilpotencyClass D.G * Group.nilpotencyClass D.G + 1) ^
          (Group.nilpotencyClass D.G + 1)) ^ 2) * d) ∧
      ∀ (z : ℝ) (y : κ → ℝ),
        roughVectorMvEval q (Option.elim · z y) =
          nativeLieGlobalLogarithm (E := N.E) (I := N.I)
            (roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hchar
              (Option.elim · z (fun k => u k+K*y k))) := by
  intro N
  obtain ⟨q, hq, he⟩ := roughNativeKernelMap_log_polynomial D S hS χ hχ hQ V hVr j
    hVS hχV a m P hP hchar p hp d ha hm hd
  let u' : Option κ → ℝ := (Option.elim · 0 u)
  let k' : Option κ → ℝ := (Option.elim · 1 (fun _ => K))
  refine ⟨roughVectorMvAffineSubstitution u' k' q,
    roughVectorMvAffineSubstitution_degree u' k' hq, ?_⟩
  intro z y
  rw [roughVectorMvAffineSubstitution_eval, he]
  congr 1
  apply congrArg (roughNativeKernelMap D S hS χ hχ hQ V hVr j hVS hχV a m P hP hchar)
  funext k
  cases k <;> simp only [u', k', Option.elim_none, Option.elim_some, zero_add, one_mul]

end Hindman168
