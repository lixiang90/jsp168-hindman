import Hindman168.AlternatingEnergySelection
import Hindman168.NativeSubprobApproximation

/-! Actual native coarse models chosen once per block/label, with the
same choice valid at every admissible earlier padding index. -/

namespace Hindman168
open FiniteMass Filter
universe u

theorem subprobHilbert_unit_norm (μ : ℕ → Mass ℤ)
    [∀ w, Fact (∀ a, 0 ≤ μ w a)] (U : Ultrafilter ℕ)
    (hprob : ∀ w, total (μ w) ≤ 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hf : ∀ w y, y ∈ (μ w).support → 0 ≤ f.val w y ∧ f.val w y ≤ 1) :
    ‖hilbertFamilyToCompletion _ U f‖ ≤ 1 := by
  apply hilbertFamilyToCompletion_norm_le _ U f zero_le_one
  intro w
  apply finiteMassL2_norm_le_subprob (μ w) (hprob w) (f.val w) zero_le_one
  intro y hy
  rw [abs_of_nonneg (hf w y hy).1]
  exact (hf w y hy).2

theorem native_subprob_selected_models (ι : Type*) [Fintype ι] (n s : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (M : ℕ) (F : MasterParameterFamily)
      (μ : ℕ → ℕ → Mass ℤ) [∀ i w, Fact (∀ y, 0 ≤ μ i w y)]
      (_hprob : ∀ i w, total (μ i w) ≤ 1) (U : Ultrafilter ℕ)
      (gap : ℕ → ℕ → Fin M),
      (∀ l k, l ≤ k → ∀ w, F.gap w (gap l w).val ∣ F.gap w (gap k w).val) →
      ∀ f : Finset ℕ → (i : ℕ) → ι → boundedHilbertFamilies (fun w => FiniteMassL2 (μ i w)),
      (∀ T i a w y, y ∈ (μ i w).support → 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < N) ∧
        ∀ T : Finset ℕ, ∀ b : Fin n, ∀ a : ι,
          ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (μ (energyPrincipal e b) w)),
            NativePieceRepresented.{u} s F (gap (energyPadding e b)) (fun w y => t.val w y) ∧
            (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (μ (energyPrincipal e b)) U
                (gap (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U t‖ < ε ∧
            ∀ v : Fin n, v ≤ b → T ⊆ energyPrincipalSet e →
              (∀ y ∈ T, y < energyPrincipal e v) →
              ‖(nativeNilHilbertSubspace.{u} s F (μ (energyPrincipal e b)) U
                  (gap (energyPadding e v))).starProjection
                  (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a) -
                    hilbertFamilyToCompletion _ U t)‖ ≤ 2 * ε := by
  obtain ⟨N, hN⟩ := alternating_energy_selection ι n (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro M F μ inst hprob U gap hdiv f hf
  let V := fun i l => nativeNilHilbertSubspace.{u} s F (μ i) U (gap l)
  let x := fun T i a => hilbertFamilyToCompletion _ U (f T i a)
  obtain ⟨e, heN, he⟩ := hN (fun T l i a => ‖(V i l).starProjection (x T i a)‖ ^ 2)
    (fun T l i a => projection_energy_unit_interval (V i l) (x T i a)
      (subprobHilbert_unit_norm (μ i) U (hprob i) (f T i a) (hf T i a)))
  refine ⟨e, heN, ?_⟩
  intro T b a
  obtain ⟨t, ht, hb, ha⟩ := nativeSubprob_clipped_approximation.{u} s F
    (μ (energyPrincipal e b)) U (gap (energyPadding e b)) (hprob _)
    (f T (energyPrincipal e b) a) (hf T _ a) hε
  refine ⟨t, ht, hb, ha, ?_⟩
  intro v hvb hT hbefore
  have henergy := (le_abs_self _).trans (he v b hvb T hT hbefore a).le
  exact nested_projection_model_error _ _
    (nativeNilHilbertSubspace_refine s F (μ (energyPrincipal e b)) U _ _
      (hdiv _ _ (energyPadding_mono e hvb))) _ _
    (nativeHilbertRepresentation_mem_closed s F (μ (energyPrincipal e b)) U _ ⟨t, ht, rfl⟩)
    hε.le henergy ha.le

end Hindman168

