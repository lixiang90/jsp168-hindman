import Hindman168.WeightedHaarGeneratedAlgebra
import Hindman168.MixedDualHilbertClipping
import Hindman168.UltrafilterBoundedDiagonal

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, Fintype (G w)] [∀ w, Nonempty (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (hs : ∀ w, ∑ c, p w c = 1)
  (V : Submodule ℝ (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U))
  (hone : hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily (G := G) p hs
    (fun _ _ _ => 1) 1 zero_le_one (by simp)) ∈ V)
  (hmul : ∀ u : boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    ∀ hu : ∀ w c x, |u.val w (c, x)| ≤ 1, hilbertFamilyToCompletion _ U u ∈ V →
    ∀ f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    hilbertFamilyToCompletion _ U f ∈ V →
      hilbertFamilyToCompletion _ U
        (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f) ∈ V)

include hone hmul

/-- Powers of an actual uniformly bounded member of a unit multiplier algebra
have actual representatives in the same closed space. -/
theorem weightedHaarHilbert_algebra_power_representatives
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ V) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w c x, |f.val w (c, x)| ≤ B) :
    ∃ a : ℕ → boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ n, hilbertFamilyToCompletion _ U (a n) ∈ V) ∧
      ∀ n w c x, (a n).val w (c, x) = f.val w (c, x) ^ n := by
  let a := fun n => weightedHaarBoundedFamily p hs
    (fun w c x => f.val w (c, x) ^ n) (B ^ n) (pow_nonneg hB n) (by
      intro w c x
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb w c x) n)
  let C := B + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hCB : B ≤ C := by dsimp only [C]; linarith
  let u := C⁻¹ • f
  have hu : ∀ w c x, |u.val w (c, x)| ≤ 1 := by
    intro w c x
    change |C⁻¹ * f.val w (c, x)| ≤ 1
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hC.le)]
    calc
      _ ≤ C⁻¹ * B := mul_le_mul_of_nonneg_left (hb w c x) (inv_nonneg.mpr hC.le)
      _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hCB (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hum : hilbertFamilyToCompletion _ U u ∈ V := by
    change (hilbertFamilyCompletionLinearMap _ U) (C⁻¹ • f) ∈ V
    rw [map_smul]
    exact V.smul_mem _ hf
  refine ⟨a, ?_, fun _ _ _ _ => rfl⟩
  intro n
  induction n with
  | zero =>
    have heq : a 0 = weightedHaarBoundedFamily (G := G) p hs
        (fun _ _ _ => 1) 1 zero_le_one (by simp) := by
      apply Subtype.ext
      funext w z
      exact pow_zero _
    rw [heq]
    exact hone
  | succ n ih =>
    have hm := hmul u hu hum (a n) ih
    have heq : a (n + 1) = C • weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu (a n) := by
      apply Subtype.ext
      funext w z
      change f.val w z ^ (n + 1) = C * (C⁻¹ * f.val w z * f.val w z ^ n)
      calc
        _ = f.val w z * f.val w z ^ n := by rw [pow_succ, mul_comm]
        _ = (C * C⁻¹) * (f.val w z * f.val w z ^ n) := by rw [mul_inv_cancel₀ hC.ne', one_mul]
        _ = _ := by ring
    rw [heq]
    change (hilbertFamilyCompletionLinearMap _ U) (C • _) ∈ V
    rw [map_smul]
    exact V.smul_mem _ hm

theorem weightedHaarHilbert_algebra_polynomial_representative
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ V) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w c x, |f.val w (c, x)| ≤ B) (P : Polynomial ℝ) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      hilbertFamilyToCompletion _ U t ∈ V ∧
      ∀ w c x, t.val w (c, x) = P.eval (f.val w (c, x)) := by
  obtain ⟨a, ha, hval⟩ := weightedHaarHilbert_algebra_power_representatives p U hs V hone hmul f hf B hB hb
  let t := ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • a k
  refine ⟨t, ?_, ?_⟩
  · change (hilbertFamilyCompletionLinearMap _ U) t ∈ V
    simp only [t, map_sum, map_smul]
    exact V.sum_mem (fun k _ => V.smul_mem _ (ha k))
  · intro w c x
    simp only [t, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply]
    change (∑ k ∈ Finset.range (P.natDegree + 1),
      (fun z : κ w × G w => P.coeff k * (a k).val w z)) (c, x) = _
    simp only [Finset.sum_apply, hval, Polynomial.eval_eq_sum_range]

variable [∀ w, AddCommGroup (G w)]

theorem weightedHaarHilbert_algebra_continuous_comp_mem
    (hclosed : IsClosed (V : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)))
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ V) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w c x, |f.val w (c, x)| ≤ B)
    (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Set.Icc (-B) B))
    (ht : ∀ w c x, t.val w (c, x) = ψ (f.val w (c, x))) :
    hilbertFamilyToCompletion _ U t ∈ V := by
  apply hclosed.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn (-B) B ψ hψ (ε / 2) (by positivity)
  obtain ⟨a, ha, heval⟩ := weightedHaarHilbert_algebra_polynomial_representative p U hs V hone hmul f hf B hB hb P
  refine ⟨hilbertFamilyToCompletion _ U a, ha, ?_⟩
  rw [dist_eq_norm]
  refine (weightedHaarHilbert_uniform_distance_le p U hs t a (ε / 2) (by positivity) ?_).trans_lt (by linarith)
  intro w c x
  rw [ht, heval, abs_sub_comm]
  exact (hP _ (abs_le.mp (hb w c x))).le

variable [V.HasOrthogonalProjection]

theorem weightedHaarHilbert_algebra_projection_unit_approximation
    (A : Set (boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))))
    (hA : ∀ a ∈ A, ∀ w c x, |a.val w (c, x)| ≤ 1)
    (hV : V = (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).topologicalClosure)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t ∈ V ∧
      ‖V.starProjection (hilbertFamilyToCompletion _ U f) - hilbertFamilyToCompletion _ U t‖ < ε := by
  obtain ⟨t, _, B, hB, hb, hm, he⟩ := weightedHaarHilbert_generated_closed_approximation p U A hA V hV
    (V.starProjection_apply_mem (hilbertFamilyToCompletion _ U f)) hε
  have hclosed : IsClosed (V : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)) := by
    rw [hV]
    exact (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).isClosed_topologicalClosure
  have hc := weightedHaarHilbert_algebra_continuous_comp_mem p U hs V hone hmul hclosed
    t (weightedHaarClipFamily p hs t) hm B hB hb unitIntervalClip
    unitIntervalClip_lipschitz.continuous.continuousOn (fun _ _ _ => rfl)
  refine ⟨weightedHaarClipFamily p hs t, fun _ _ _ => unitIntervalClip_bounds _, hc, ?_⟩
  exact (projection_clipping_distance_le V (hilbertFamilyToCompletion _ U f)
    (hilbertFamilyToCompletion _ U t) (hilbertFamilyToCompletion _ U (weightedHaarClipFamily p hs t))
    hm hc (weightedHaarHilbert_clip_distance_le p U hs f t hf)).trans_lt he

theorem weightedHaarHilbert_algebra_projection_exact_representative
    (hU : (U : Filter ℕ) ≤ atTop)
    (A : Set (boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))))
    (hA : ∀ a ∈ A, ∀ w c x, |a.val w (c, x)| ≤ 1)
    (hV : V = (Submodule.span ℝ (hilbertFamilyToCompletion _ U '' A)).topologicalClosure)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t = V.starProjection (hilbertFamilyToCompletion _ U f) := by
  have ha (n : ℕ) := weightedHaarHilbert_algebra_projection_unit_approximation p U hs V hone hmul A hA hV f hf
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose a hb _ he using ha
  have hnorm : ∀ n w, ‖(a n).val w‖ ≤ 1 := by
    intro n w
    apply finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ zero_le_one
    intro z _
    rw [abs_of_nonneg (hb n w z.1 z.2).1]
    exact (hb n w z.1 z.2).2
  obtain ⟨t, _, ht, hrep⟩ := ultrafilterHilbert_bounded_diagonal _ U hU
    (fun w t => ∀ c x, 0 ≤ t (c, x) ∧ t (c, x) ≤ 1)
    (V.starProjection (hilbertFamilyToCompletion _ U f)) a 1 zero_le_one hnorm (fun n w => hb n w) he
  exact ⟨t, ht, hrep⟩

end Hindman168
