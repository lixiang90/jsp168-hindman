import Hindman168.RoughNativeKernelSpatialPolynomial
import Hindman168.RoughNativeKernelDegreeBound
import Hindman168.RoughFiniteLabelThinning
import Hindman168.RoughJointProgressionPolynomial

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_kernel_label_thinning {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (hS : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ (nativeLieSubalgebraModel S))
    (χ : D.E →ₗ[ℝ] ℝ)
    (hχ : ∀ x ∈ nativeLieSubalgebraModel S, ∀ y ∈ nativeLieSubalgebraModel S,
      χ (nativeLieAdjointDifferential (I := D.I) (G := D.G) x y) = 0)
    (hQ : ∀ x ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ,
      ∃ r : ℚ, χ x = (r : ℝ))
    (V : D.E) (hVr : V ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (hVS : V ∈ nativeLieSubalgebraModel S) (hχV : χ V = 1)
    (K H : ℕ) (hH : 0 < H) :
    ∃ N : ℕ, 0 < N ∧ ∀
    (a m : MvPolynomial (Option κ) ℝ) (P : (Option κ → ℝ) → D.G)
    (hP : ∀ x, P x ∈ nativeLieSubalgebraSubgroup (E := D.E) S)
    (hchar : ∀ x, nativeLieLogarithmCharacter (I := D.I) (G := D.G) χ (P x) =
      MvPolynomial.eval x a + MvPolynomial.eval x m)
    (p : RoughVectorMvPolynomial (Option κ) D.E)
    (_hp : ∀ x, roughVectorMvEval p x = nativeLieGlobalLogarithm (E := D.E) (I := D.I) (P x))
    (d : ℕ) (_ha : a.totalDegree ≤ d) (_hm : m.totalDegree ≤ d) (_hd : RoughVectorMvDegreeLE p d), ∀ bad : ℕ → ((κ → Fin K) × Fin K) → Prop,
      (∀ z : ℕ, z < N → ∃ label, bad z label) →
      ∃ a0 b : ℕ, ∃ label : (κ → Fin K) × Fin K,
        let u : κ → ℝ := fun k => (label.1 k).val
        let Nnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
        0 < b ∧ b ≤ N ∧ Module.finrank ℝ Nnew.E < Module.finrank ℝ D.E ∧
        (∀ z : ℕ, z < H → a0+b*z < N ∧ bad (a0+b*z) label) ∧
        ∃ pNew : RoughVectorMvPolynomial (Option κ) Nnew.E,
          RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor s*d) ∧
          ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z y) =
            nativeLieGlobalLogarithm (E := Nnew.E) (I := Nnew.I)
              (roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
                (Option.elim · ((a0 : ℝ)+(b : ℝ)*z) (fun k => u k+(K : ℝ)*y k))) := by
  obtain ⟨N, hN, hthin⟩ := rough_finite_label_thinning H hH ((κ → Fin K) × Fin K)
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd bad hbad
  obtain ⟨a0, b, label, hb, hbN, hmono⟩ := hthin bad hbad
  let Nnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
  let u : κ → ℝ := fun k => (label.1 k).val
  let Qnew : (Option κ → ℝ) → Nnew.G := fun x =>
    roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
      (Option.elim · (x none) (fun k => u k+(K : ℝ)*x (some k)))
  obtain ⟨q, hq, heq⟩ := rough_native_kernel_spatial_log_polynomial D S hS χ hχ hQ V hVr
    (label.2.val : ℤ) hVS hχV a m P hP hchar p hp d ha hm hd u (K : ℝ)
  obtain ⟨pNew, hdegree, heNew⟩ := rough_joint_progression_polynomial
    (nativeLieGlobalLogarithm (E := Nnew.E) (I := Nnew.I)) Qnew q
    (roughKernelDegreeFactor s*d) (rough_native_kernel_degree_uniform D hq) heq (a0 : ℝ) (b : ℝ)
  exact ⟨a0, b, label, hb, hbN,
    roughNativeKernelNilmanifold_finrank_lt D S hS χ hχ hQ V hVr _ hVS (by rw [hχV]; norm_num),
    hmono, pNew, hdegree, heNew⟩

end Hindman168
