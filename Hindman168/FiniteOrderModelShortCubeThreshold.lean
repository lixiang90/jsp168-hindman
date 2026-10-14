import Hindman168.MasterFixedQuotientInverseShortCube
import Hindman168.MasterModelDifferenceShortCube
import Mathlib.Algebra.Order.Field.Pi

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- One J and one positive projection threshold work for a whole finite
list of cube dimensions. Both are selected before N, all master data,
integer inputs and original prime laws. The inverse inputs are explicit. -/
theorem finite_order_model_shortCube_threshold (Q : Type*) [Fintype Q]
    (s : ℕ) (dim : Q → ℕ)
    (hinverse : ∀ q, HasNativePeriodicIntervalInverse.{u} s (2 ^ dim q + 2 ^ dim q - 1))
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ q : Q, ∀ {n M : ℕ} (hM : 0 < M)
        (D : Finset (MvPolynomial (Fin n) ℤ)) (hD : ∀ p ∈ D, p ≠ 0)
        (pol : MvPolynomial (Fin n) ℤ) (_hpol : pol ∈ D)
        (T : Finset (MvPolynomial (Fin n) ℤ)) (_hT : ∀ p ∈ T, p ≠ 0) (_hpolT : pol ∈ T)
        (l i : ℕ) (_hl : l < M) (_hi : i < M) (_hli : l ≤ i),
      let F := constructedMasterFamily M D hD
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
        (_ht : ∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F i) U
        (masterGapIndex M hM l)).starProjection
          (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        let μ := conditionMass (dyadicPoolTupleMass (fun _ : Fin n => F.pool w l))
          (primeSampleGood T)
        expectation μ (fun x => |integerPredictionShortCubeStatistic w (F.modulus w : ℕ)
          (F.gap w l) (F.cutoff w i) (dim q) J pol (fun y => f.val w y - t.val w y) x|) < η := by
  classical
  let B : ℕ := ∑ q, dim q
  obtain ⟨J, hlarge⟩ := exists_nat_gt (16 * ((B : ℝ) + 1) / η)
  have hJR : (0 : ℝ) < J := (div_pos (by positivity) hη).trans hlarge
  have hJ : 0 < J := by exact_mod_cast hJR
  have hcost (q : Q) : 4 * (dim q : ℝ) / J < η / 4 := by
    have hdq : (dim q : ℝ) ≤ B := by
      exact_mod_cast (Finset.single_le_sum (fun a _ => Nat.zero_le (dim a)) (Finset.mem_univ q))
    apply (div_lt_iff₀ hJR).mpr
    have hh := (div_lt_iff₀ hη).mp hlarge
    nlinarith
  have each q := master_inverse_shortCube_fixed_quotient_threshold
    s (dim q) J hJ (hinverse q) (η / 2) (by positivity)
  choose bound hbound he using each
  obtain ⟨κ, hκ, hbelow⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Q => (0 : ℝ))
    (y := bound) hbound
  refine ⟨J, hJ, κ, hκ, ?_⟩
  intro q n M hM D hD pol hpol T hT hpolT l i hl hi hli F U hU f t hf ht hp
  let gap : ℕ → Fin M := fun _ => ⟨l, hl⟩
  let pivot : ℕ → Fin M := fun _ => ⟨i, hi⟩
  have hmap : masterGapIndex M hM l = gap := by
    funext w
    apply Fin.ext
    exact masterGapIndex_val M hM l w hl
  have hb : ∀ w y, |(f - t).val w y| ≤ 1 := by
    intro w y
    change |f.val w y - t.val w y| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hf w y).1, (ht w y).2],
      by linarith [(hf w y).2, (ht w y).1]⟩
  have hs : hilbertFamilyToCompletion _ U (f - t) =
      hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
    (hilbertFamilyCompletionLinearMap _ U).map_sub f t
  have hpq : ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F i) U
      gap).starProjection (hilbertFamilyToCompletion _ U (f - t))‖ < bound q := by
    rw [hs, ← hmap]
    exact hp.trans (by simpa only [zero_add] using hbelow q)
  have hx := he q D hD pol hpol T hT hpolT gap pivot
    (Eventually.of_forall (fun _ => hli)) U hU (f - t) hb hpq
  filter_upwards [hx] with w hw
  exact hw.trans (by linarith [hcost q])

end Hindman168
