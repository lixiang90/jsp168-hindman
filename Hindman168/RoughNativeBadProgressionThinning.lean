import Hindman168.RoughNativeKernelSpatialPolynomial
import Hindman168.RoughNativeKernelDegreeBound
import Hindman168.RoughFiniteLabelThinning
import Hindman168.RoughJointProgressionPolynomial

import Hindman168.RoughNativeBadIndex
import Hindman168.RoughNativeKernelLabelThinning

namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_bad_progression_thinning {κ : Type*} [Fintype κ] {s : ℕ}
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
      ∃ (a0 b : ℕ) (u : κ → Fin K) (j : Fin K),
        let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (j.val : ℤ)
        ∃ Qnew : (Option κ → ℝ) → Dnew.G,
        0 < b ∧ b ≤ N ∧ Module.finrank ℝ Dnew.E < Module.finrank ℝ D.E ∧
        (∀ x, Qnew x = roughNativeKernelMap D S hS χ hχ hQ V hVr (j.val : ℤ) hVS hχV a m P hP hchar
          (Option.elim · ((a0 : ℝ)+(b : ℝ)*x none)
            (fun k => ((u k).val : ℝ)+(K : ℝ)*x (some k)))) ∧
        (∃ pNew : RoughVectorMvPolynomial (Option κ) Dnew.E,
          RoughVectorMvDegreeLE pNew (roughKernelDegreeFactor s*d) ∧
          ∀ (z : ℝ) (y : κ → ℝ), roughVectorMvEval pNew (Option.elim · z y) =
            nativeLieGlobalLogarithm (E := Dnew.E) (I := Dnew.I) (Qnew (Option.elim · z y))) ∧
        0 < b*diff ∧ (∀ prime : ℕ, prime.Prime → prime ∣ b*diff → prime ≤ w) ∧
        ∀ z : ℕ, z < H → a0+b*z < N ∧
          Scale ≤ ((t+diff*a0)+(b*diff)*z : ℕ) ∧
          ((t+diff*a0)+(b*diff)*z : ℕ) < 2*Scale ∧
          (primorial w).Coprime ((t+diff*a0)+(b*diff)*z) ∧
          RoughNativeBadIndex Dnew Qnew z ((t+diff*a0)+(b*diff)*z) Z c C L B η := by
  obtain ⟨N, hN, hthin⟩ := rough_native_kernel_label_thinning (κ := κ) D S hS χ hχ hQ V hVr hVS hχV K H hH
  refine ⟨N, hN, ?_⟩
  intro a m P hP hchar p hp d ha hm hd w t diff Z Scale c C L B η hdiff hNw hsmooth hsize hrough hbad
  let bad := fun z : ℕ => fun label : (κ → Fin K) × Fin K =>
    RoughNativeBadIndex (roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ))
      (fun x => roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
        (Option.elim · (x none) (fun k => ((label.1 k).val : ℝ)+(K : ℝ)*x (some k))))
      z (t+diff*z) Z c C L B η
  have hex : ∀ z : ℕ, z < N → ∃ label, bad z label := by
    intro z hz
    obtain ⟨u, j, hh⟩ := hbad z hz
    exact ⟨(u,j), hh⟩
  obtain ⟨a0, b, label, hb, hbN, hdim, hmono, pNew, hdegree, hlog⟩ :=
    hthin a m P hP hchar p hp d ha hm hd bad hex
  let Dnew := roughNativeKernelNilmanifold D S hS χ hχ hQ V hVr (label.2.val : ℤ)
  let Qbase : (Option κ → ℝ) → Dnew.G := fun x =>
    roughNativeKernelMap D S hS χ hχ hQ V hVr (label.2.val : ℤ) hVS hχV a m P hP hchar
      (Option.elim · (x none) (fun k => ((label.1 k).val : ℝ)+(K : ℝ)*x (some k)))
  let Qnew : (Option κ → ℝ) → Dnew.G := fun x =>
    Qbase (Option.elim · ((a0 : ℝ)+(b : ℝ)*x none) (fun k => x (some k)))
  obtain ⟨hbdiff, hsmooth', hvalues⟩ := rough_smooth_progression_reparametrization
    w N H t diff a0 b Scale hdiff hb hbN hNw hsmooth
    (fun z hz => (hmono z hz).1) hsize hrough
  refine ⟨a0, b, label.1, label.2, Qnew, hb, hbN, hdim, fun _ => rfl,
    ⟨pNew, hdegree, ?_⟩, hbdiff, hsmooth', ?_⟩
  · simpa only [Qnew, Qbase, Option.elim_none, Option.elim_some] using hlog
  · intro z hz
    obtain ⟨he, hlow, hhigh, hr⟩ := hvalues z hz
    refine ⟨(hmono z hz).1, hlow, hhigh, hr, ?_⟩
    have hh := rough_native_bad_index_reparametrize Dnew Qbase a0 b z (t+diff*(a0+b*z))
      Z c C L B η (hmono z hz).2
    simpa only [he] using hh

end Hindman168
