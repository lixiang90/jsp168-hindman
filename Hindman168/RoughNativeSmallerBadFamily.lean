import Hindman168.RoughNativeKernelSpatialPolynomial
import Hindman168.RoughNativeKernelDegreeBound
import Hindman168.RoughFiniteLabelThinning
import Hindman168.RoughJointProgressionPolynomial

import Hindman168.RoughNativeBadIndex
import Hindman168.RoughNativeKernelLabelThinning

import Hindman168.RoughNativeBadFamily
import Hindman168.RoughNativeBadProgressionThinning

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_smaller_bad_family {κ : Type*} [Fintype κ] {s : ℕ}
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
    (d : ℕ) (_ha : a.totalDegree ≤ d) (_hm : m.totalDegree ≤ d) (_hd : RoughVectorMvDegreeLE p d),
    ∀ (w t diff : ℕ) (Z Scale c C : ℝ) (L : NNReal) (B η : ℝ),
      0 < diff → N ≤ w →
      (∀ prime : ℕ, prime.Prime → prime ∣ diff → prime ≤ w) →
      (∀ z : ℕ, z < N → Scale ≤ (t+diff*z : ℕ) ∧ (t+diff*z : ℕ) < 2*Scale) →
      (∀ z : ℕ, z < N → (primorial w).Coprime (t+diff*z)) →
      (∀ z : ℕ, z < N → ∃ (u : κ → Fin K) (j : Fin K),
        RoughNativeBadIndex (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ))
          (fun x => roughNativeKernelMap D S hS χ hχ hQ V hVr (j.val : ℤ) hVS hχV a m P hP hchar
            (Option.elim · (x none) (fun k => ((u k).val : ℝ)+(K : ℝ)*x (some k))))
          z (t+diff*z) Z c C L B η) →
      ∃ j : Fin K,
        let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
        Module.finrank ℝ Dnew.E < Module.finrank ℝ D.E ∧
        RoughNativeBadFamily (κ := κ) Dnew H w Scale Z
          (roughKernelDegreeFactor s*d) c C L B η := by
  obtain ⟨N, hN, hthin⟩ := rough_native_bad_progression_thinning (κ := κ) D S hS χ hχ hQ V hVr hVS hχV K H hH
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η hdiff hNw hsmooth hsize hrough hbad
  obtain ⟨a0, b, u, j, Qnew, hb, hbN, hdim, hQnew, pNewData, hdiff', hsmooth', hindices⟩ :=
    hthin a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η
      hdiff hNw hsmooth hsize hrough hbad
  obtain ⟨pNew, hdeg, hlog⟩ := pNewData
  refine ⟨j, hdim, Qnew, pNew, t+diff*a0, b*diff, hdeg, hlog, hdiff', hsmooth', ?_⟩
  intro z hz
  exact (hindices z hz).2

end Hindman168
