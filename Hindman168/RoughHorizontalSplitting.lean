import Hindman168.RoughSpatialCoefficientModels
import Hindman168.RoughJointCoefficientThinning

namespace Hindman168
open Polynomial Filter
open scoped Topology BigOperators

theorem rough_coefficient_model_restrict {w N H q e : ℕ} {Z K : ℝ}
    {theta : ℝ[X]} {M : ℚ[X]} (h : RoughCoefficientModel w N q e Z K theta M)
    (hHN : H ≤ N) : RoughCoefficientModel w H q e Z K theta M :=
  ⟨h.1, h.2.1, fun z hz => h.2.2 z (hz.trans_le hHN)⟩

theorem rough_horizontal_coefficient_splitting {α κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (q q0 H : ℕ) (hH : 0 < H)
    (he : ∀ I ∈ s, 0 < (∑ j, I j) ∧ (∑ j, I j) ≤ q)
    (A0 : ℝ) (hA : 0 < A0) :
    ∃ L : ℕ, 2 * q + 2 ≤ L ∧ ∀ (l : Filter α) (W : α → ℕ) (S Z : α → ℝ),
      Tendsto W l atTop → PowerDominates l Z S →
      (∀ᶠ w in l, 1 ≤ S w) → (∀ᶠ w in l, 0 < Z w) →
      ∀ᶠ w in l, ∀ (t m : ℕ) (theta : (κ → ℕ) → ℝ[X]) (P : ℝ[X])
        (p : (κ → ℕ) → ℕ → ℕ) (r : (κ → ℕ) → ℕ → κ → ℕ),
        P.natDegree ≤ q0 → 0 < m →
        (∀ v, v.Prime → v ∣ m → v ≤ W w) →
        (∀ z : ℕ, z < L → S w ≤ (t + m * z : ℕ) ∧ (t + m * z : ℕ) < 2 * S w) →
        (∀ z : ℕ, z < L → (primorial (W w)).Coprime (t + m * z)) →
        (∀ I ∈ s, ((C (t : ℝ) + C (m : ℝ) * X) ^ (∑ j, I j) * theta I).natDegree ≤ q) →
        (∀ I ∈ s, ∀ z, z < L → p I z = 1 ∨ p I z = t + m * z) →
        (∀ I ∈ s, ∀ z, z < L → ∀ j, r I z j ≤ p I z) →
        (∀ I ∈ s, ∀ z, z < L →
          ‖(((p I z : ℝ) ^ (∑ j, I j) *
            (∑ J ∈ s, (roughBinomialWeight I J (r I z) : ℝ) * (theta J).eval (z : ℝ)) : ℝ) : UnitAddCircle)‖ ≤
              A0 * ((p I z : ℝ) / Z w) ^ (∑ j, I j)) →
        ∃ a b : ℕ, ∃ M0 : ℚ[X], ∃ M : (κ → ℕ) → ℚ[X],
          0 < b ∧ b ≤ L ∧ (∀ z : ℕ, z < H → a + b * z < L) ∧
          0 < m * b ∧ (∀ v, v.Prime → v ∣ m * b → v ≤ W w) ∧
          (∀ z : ℕ, z < H → S w ≤ ((t + m * a) + (m * b) * z : ℕ) ∧
            ((t + m * a) + (m * b) * z : ℕ) < 2 * S w) ∧
          (∀ z : ℕ, z < H → (primorial (W w)).Coprime ((t + m * a) + (m * b) * z)) ∧
          M0.natDegree ≤ q0 ∧
          (∀ j v, v.Prime → v ∣ (M0.coeff j).den → v ≤ W w) ∧
          (∀ z : ℕ, z < H → M0.eval (z : ℚ) = (⌊P.eval ((a + b * z : ℕ) : ℝ)⌋ : ℚ) ∧
            0 ≤ P.eval ((a + b * z : ℕ) : ℝ) - ((M0.eval (z : ℚ) : ℚ) : ℝ) ∧
            P.eval ((a + b * z : ℕ) : ℝ) - ((M0.eval (z : ℚ) : ℚ) : ℝ) < 1) ∧
          ∀ I ∈ s, RoughCoefficientModel (W w) H q (∑ j, I j) (Z w)
            (roughDescentConstant q s.card A0 (2 ^ q) q)
            ((theta I).comp (C (a : ℝ) + C (b : ℝ) * X)) (M I) := by
  obtain ⟨N, _hN, hthin⟩ := rough_joint_coefficient_thinning s q0 H hH
  let L := max N (2 * q + 2)
  have hNL : N ≤ L := le_max_left _ _
  have hL : 2 * q + 2 ≤ L := le_max_right _ _
  refine ⟨L, hL, ?_⟩
  intro l W S Z hW hg hS hZ
  have hmodels := rough_spatial_coefficient_models hW hg hS hZ s q L hL he A0 hA
  filter_upwards [hmodels, hW.eventually (eventually_ge_atTop N)] with w hw hNw
  intro t m theta P p r hP hm hmsmooth hprog hrough hdeg hp hr hobs
  obtain ⟨Mold, hOld⟩ := hw t m theta p r hm hmsmooth hprog hrough hdeg hp hr hobs
  obtain ⟨a, b, M0, hb, hbN, hindex, hM0, hden, hval, hnew⟩ :=
    hthin (W w) q (fun I => ∑ j, I j) (Z w)
      (roughDescentConstant q s.card A0 (2 ^ q) q) theta Mold P hNw hP
      (fun I hi => rough_coefficient_model_restrict (hOld I hi) hNL)
  have hidx : ∀ z : ℕ, z < H → a + b * z < L := fun z hz => (hindex z hz).trans_le hNL
  obtain ⟨hmb, hsmooth, hinterval, hcoprime⟩ :=
    rough_progression_reparametrize hm hb (hbN.trans hNw) hmsmooth hprog hrough hidx
  exact ⟨a, b, M0, fun I => (Mold I).comp (C (a : ℚ) + C (b : ℚ) * X),
    hb, hbN.trans hNL, hidx, hmb, hsmooth, hinterval, hcoprime, hM0, hden, hval, hnew⟩

end Hindman168
