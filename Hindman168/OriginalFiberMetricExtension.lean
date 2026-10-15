import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Quantitative extension of unit-bounded complex observables.
The radial clipping map is the identity on the closed unit disk. -/

namespace Hindman168.OriginalFiberMetric
open scoped NNReal

noncomputable def radialClip (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

theorem radialClip_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : radialClip z = z := by
  simp [radialClip, max_eq_left hz]

theorem radialClip_norm_le (z : ℂ) : ‖radialClip z‖ ≤ 1 := by
  have ha : (0 : ℝ) < max 1 ‖z‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  rw [radialClip, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_one ha).mpr (le_max_right _ _)

theorem radialClip_dist_le_of_norm_le (x y : ℂ) (hxy : ‖x‖ ≤ ‖y‖) :
    dist (radialClip x) (radialClip y) ≤ 2 * dist x y := by
  let a : ℝ := max 1 ‖x‖
  let b : ℝ := max 1 ‖y‖
  have ha : 1 ≤ a := le_max_left _ _
  have hb : 1 ≤ b := le_max_left _ _
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hab : a ≤ b := max_le_max le_rfl hxy
  have hinv : b⁻¹ ≤ a⁻¹ := inv_anti₀ hapos hab
  have hx : ‖x‖ ≤ a := le_max_right _ _
  have hdiff : b - a ≤ ‖x - y‖ := by
    have hn := norm_sub_norm_le y x
    rw [norm_sub_rev] at hn
    have hba : b ≤ a + ‖x - y‖ := by
      apply max_le
      · linarith [norm_nonneg (x - y)]
      · linarith
    linarith
  have heq : a⁻¹ • x - b⁻¹ • y =
      b⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • x := by
    simp only [smul_sub, sub_smul]
    abel
  have hcoef : (a⁻¹ - b⁻¹) * a = b⁻¹ * (b - a) := by
    field_simp
  have hsecond : (a⁻¹ - b⁻¹) * ‖x‖ ≤ b⁻¹ * ‖x - y‖ := by
    calc
      _ ≤ (a⁻¹ - b⁻¹) * a := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hinv)
      _ = b⁻¹ * (b - a) := hcoef
      _ ≤ b⁻¹ * ‖x - y‖ := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hbpos.le)
  have hfirst : b⁻¹ * ‖x - y‖ ≤ ‖x - y‖ := by
    have hi : b⁻¹ ≤ 1 := (inv_le_one₀ hbpos).mpr hb
    simpa using mul_le_mul_of_nonneg_right hi (norm_nonneg (x - y))
  rw [dist_eq_norm, dist_eq_norm]
  change ‖a⁻¹ • x - b⁻¹ • y‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖b⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • x‖ := norm_add_le _ _
    _ = b⁻¹ * ‖x - y‖ + (a⁻¹ - b⁻¹) * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hbpos.le), abs_of_nonneg (sub_nonneg.mpr hinv)]
    _ ≤ 2 * ‖x - y‖ := by linarith

theorem radialClip_lipschitz : LipschitzWith 2 radialClip := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (radialClip x) (radialClip y) ≤ (2 : ℝ) * dist x y
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · exact radialClip_dist_le_of_norm_le x y hxy
  · simpa only [dist_comm] using radialClip_dist_le_of_norm_le y x hyx

/-- McShane extension of both real coordinates followed by radial clipping.
The factor four is uniform, and the unit bound and prescribed values are exact. -/
theorem extend_unit_complex {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {f : X → ℂ} {A : ℝ≥0}
    (hf : LipschitzOnWith A f S) (hnorm : ∀ x ∈ S, ‖f x‖ ≤ 1) :
    ∃ F : X → ℂ, LipschitzWith (4 * A) F ∧
      (∀ x, ‖F x‖ ≤ 1) ∧ Set.EqOn f F S := by
  have hr : LipschitzOnWith A (fun x => (f x).re) S := by
    simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hf
  have hi : LipschitzOnWith A (fun x => (f x).im) S := by
    simpa only [one_mul, Function.comp_def, RCLike.im_eq_complex_im] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hf
  obtain ⟨r, hrlip, hre⟩ := hr.extend_real
  obtain ⟨i, hilip, hie⟩ := hi.extend_real
  let F₀ : X → ℂ := fun x => ⟨r x, i x⟩
  have hF₀ : LipschitzWith (2 * A) F₀ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hrxy := hrlip.dist_le_mul x y
    have hixy := hilip.dist_le_mul x y
    rw [Real.dist_eq] at hrxy hixy
    have hn := Complex.norm_le_abs_re_add_abs_im (F₀ x - F₀ y)
    simp only [F₀, Complex.sub_re, Complex.sub_im] at hn
    rw [dist_eq_norm]
    push_cast
    linarith
  have heq (x : X) (hx : x ∈ S) : f x = F₀ x :=
    Complex.ext (hre hx) (hie hx)
  refine ⟨radialClip ∘ F₀, ?_, fun x => radialClip_norm_le _, ?_⟩
  · convert radialClip_lipschitz.comp hF₀ using 1
    ring
  · intro x hx
    change f x = radialClip (F₀ x)
    rw [← heq x hx, radialClip_eq_self (hnorm x hx)]

/-- Apply the extension to an observable on an embedded metric space.
The inverse metric bound is an explicit input here, proved separately for
the BCH fibre inclusion; this theorem does not assert that bound. -/
theorem extend_observable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    (c : X → Y) {C A : ℝ≥0} (hc : AntilipschitzWith C c)
    (G : X → ℂ) (hG : LipschitzWith A G) (hnorm : ∀ x, ‖G x‖ ≤ 1) :
    ∃ F : C(Y, ℂ), LipschitzWith (4 * (A * C)) F ∧
      (∀ y, ‖F y‖ ≤ 1) ∧ ∀ x, F (c x) = G x := by
  classical
  let f : Y → ℂ := fun y => if hy : y ∈ Set.range c then G (Classical.choose hy) else 0
  have hfc (x : X) : f (c x) = G x := by
    have hx : c x ∈ Set.range c := ⟨x, rfl⟩
    dsimp only [f]
    rw [dif_pos hx]
    congr 1
    exact hc.injective (Classical.choose_spec hx)
  have hf : LipschitzOnWith (A * C) f (Set.range c) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hfc, hfc]
    calc
      _ ≤ A * dist x y := hG.dist_le_mul x y
      _ ≤ A * (C * dist (c x) (c y)) :=
        mul_le_mul_of_nonneg_left (hc.le_mul_dist x y) A.coe_nonneg
      _ = _ := by simp only [NNReal.coe_mul]; ring
  obtain ⟨F, hF, hnF, hEq⟩ := extend_unit_complex hf (by
    rintro _ ⟨x, rfl⟩
    rw [hfc]
    exact hnorm x)
  refine ⟨⟨F, hF.continuous⟩, hF, hnF, ?_⟩
  intro x
  exact (hEq (Set.mem_range_self x)).symm.trans (hfc x)

end Hindman168.OriginalFiberMetric
