import Hindman168.RoughExactInterpolationModOne
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Correct one-dimensional slab volume bound with its TRUE finite integer
cover budget. This replaces the unsupported budget-free source estimate;
the full torus-neighborhood argument is not claimed by this module. -/
namespace Hindman168
open MeasureTheory Set
open scoped BigOperators Classical

theorem real_affine_integer_slab_measure (S : Set ℝ) (θ z ε : ℝ) (hz : 0 < z)
    (C : Finset ℤ) (hcover : ∀ x ∈ S, ∃ k ∈ C, |θ+z*x-(k : ℝ)| ≤ ε) :
    volume S ≤ ENNReal.ofReal ((C.card : ℝ)*(2*ε/z)) := by
  let f (k : ℤ) : Set ℝ := Icc (((k : ℝ)-θ-ε)/z) (((k : ℝ)-θ+ε)/z)
  have hsub : S ⊆ ⋃ k ∈ C, f k := by
    intro x hx
    obtain ⟨k,hk,he⟩ := hcover x hx
    have ha := abs_le.mp he
    apply mem_iUnion.mpr
    refine ⟨k,mem_iUnion.mpr ⟨hk,?_⟩⟩
    exact ⟨(div_le_iff₀ hz).mpr (by linarith),(le_div_iff₀ hz).mpr (by linarith)⟩
  apply (measure_mono hsub).trans
  apply (measure_biUnion_finset_le C f).trans
  have hf : ∀ k, volume (f k)=ENNReal.ofReal (2*ε/z) := by
    intro k
    change volume (Icc (((k : ℝ)-θ-ε)/z) (((k : ℝ)-θ+ε)/z))=ENNReal.ofReal (2*ε/z)
    rw [Real.volume_Icc]
    congr 1
    ring
  simp_rw [hf]
  rw [Finset.sum_const,nsmul_eq_mul,ENNReal.ofReal_mul (Nat.cast_nonneg C.card),ENNReal.ofReal_natCast]

theorem real_affine_integer_slab_measure_small (S : Set ℝ) (θ z ε δ : ℝ) (hz : 0 < z)
    (C : Finset ℤ) (hcover : ∀ x ∈ S, ∃ k ∈ C, |θ+z*x-(k : ℝ)| ≤ ε)
    (hε : (C.card : ℝ)*(2*ε) ≤ (δ/2)*z) :
    volume S ≤ ENNReal.ofReal (δ/2) := by
  apply (real_affine_integer_slab_measure S θ z ε hz C hcover).trans
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hz).mpr hε

theorem bounded_real_circle_slab_integer_cover (T Z : ℝ) :
    ∃ K : ℕ, ∀ (θ z ε x : ℝ), |θ| ≤ T → |z| ≤ Z → ε ≤ 1 → x ∈ Icc (0 : ℝ) 1 →
      ‖((θ+z*x : ℝ) : UnitAddCircle)‖ ≤ ε →
        ∃ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), |θ+z*x-(k : ℝ)| ≤ ε := by
  obtain ⟨K,hK⟩ := exists_nat_gt (T+Z+1)
  refine ⟨K,?_⟩
  intro θ z ε x hθ hz hε hx hsmall
  obtain ⟨k,hk⟩ := (rough_mod_one_near_integer_iff (θ+z*x) ε).mp hsmall
  have hval : |θ+z*x| ≤ T+Z := by
    have hzx : |z*x| ≤ Z := by
      rw [abs_mul,abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_right (abs_nonneg z) hx.2).trans hz
    exact (abs_add_le _ _).trans (add_le_add hθ hzx)
  have hki : |(k : ℝ)| ≤ (K : ℝ) := by
    have he : (k : ℝ)=(θ+z*x)-(θ+z*x-(k : ℝ)) := by ring
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add hval hk)).trans (by linarith)
  have hbounds := abs_le.mp hki
  refine ⟨k,Finset.mem_Icc.mpr ⟨by exact_mod_cast hbounds.1,by exact_mod_cast hbounds.2⟩,hk⟩

theorem bounded_real_circle_slab_measure (T Z : ℝ) :
    ∃ K : ℕ, ∀ (θ z ε : ℝ), |θ| ≤ T → |z| ≤ Z → ε ≤ 1 → 0 < z →
      volume {x : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ ‖((θ+z*x : ℝ) : UnitAddCircle)‖ ≤ ε} ≤
        ENNReal.ofReal (((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ)*(2*ε/z)) := by
  obtain ⟨K,hcover⟩ := bounded_real_circle_slab_integer_cover T Z
  refine ⟨K,?_⟩
  intro θ z ε hθ hz hε hz0
  exact real_affine_integer_slab_measure _ θ z ε hz0 _
    (fun x hx => hcover θ z ε x hθ hz hε hx.1 hx.2)

end Hindman168
