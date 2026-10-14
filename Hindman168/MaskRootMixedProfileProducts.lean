import Hindman168.AdditiveRetainedProduct
import Hindman168.MaskRootTargetMoment

/-! Exact native B*Psi and B*Psi0*Psi1 profile products. Psi is the
full original retainedMajorant, translated by the actual root direction. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

local notation "d" => rootMomentDimension m gap t

noncomputable def shiftedRetainedProfile
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) (u : ℤ) : ℝ :=
  MaskOriginalSampling.retainedMajorant gap a C t label w
    (x, fun col => z col + MaskOriginalSampling.rootShift gap a C t w x u col) v

theorem profile_retained_product_eq
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ)
    (u : ℤ × ℤ) (bit : Bool) :
    profileProduct gap a C t label (rootMomentRetained d bit) w x z v u =
      shiftedRetainedProfile gap a C t label w x z v (rootPairValues u bit) := by
  unfold profileProduct rootMomentRetained
  have hj : Function.Injective (fun r : AdditiveNonRootCopy d =>
      Fintype.equivFin (RootSmoothedAdditiveCopy d) (rootSmoothedRetainedCopy r bit)) := by
    intro r s h
    exact rootSmoothedRetainedCopy_injective d bit ((Fintype.equivFin _).injective h)
  rw [Finset.prod_image hj.injOn]
  simp only [rootSmoothedRowEnumeration, Equiv.symm_apply_apply, rootSmoothedRetainedCopy,
    rootSmoothedCopy]
  unfold shiftedRetainedProfile MaskOriginalSampling.retainedMajorant
  rw [AdditiveRowData.retained_product_flat]

include ha hC in
theorem profile_first_product_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u,
      profileProduct gap a C t label (rootMomentFirst d) w x z v u =
        targetMajorantCube gap a C t label w x z v *
          shiftedRetainedProfile gap a C t label w x z v u.1 := by
  filter_upwards [profile_target_product_eventually gap a ha C hC t label] with w hw
  intro x hx z v u
  unfold rootMomentFirst profileProduct
  rw [Finset.prod_union (rootMomentTarget_retained_disjoint d false)]
  change profileProduct gap a C t label (rootMomentTarget d) w x z v u *
    profileProduct gap a C t label (rootMomentRetained d false) w x z v u = _
  rw [hw x hx z v u, profile_retained_product_eq]
  rfl

include ha hC in
theorem profile_second_product_eventually
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ z v u,
      profileProduct gap a C t label (rootMomentSecond d) w x z v u =
        targetMajorantCube gap a C t label w x z v *
          shiftedRetainedProfile gap a C t label w x z v u.1 *
          shiftedRetainedProfile gap a C t label w x z v u.2 := by
  filter_upwards [profile_first_product_eventually gap a ha C hC t label] with w hw
  intro x hx z v u
  have hd : Disjoint (rootMomentFirst d) (rootMomentRetained d true) :=
    Finset.disjoint_union_left.mpr
      ⟨rootMomentTarget_retained_disjoint d true, rootMomentRetained_disjoint d⟩
  unfold rootMomentSecond profileProduct
  rw [Finset.prod_union hd]
  change profileProduct gap a C t label (rootMomentFirst d) w x z v u *
    profileProduct gap a C t label (rootMomentRetained d true) w x z v u = _
  rw [hw x hx z v u, profile_retained_product_eq]
  rfl

end Hindman168.MaskRootOriginalSampling
