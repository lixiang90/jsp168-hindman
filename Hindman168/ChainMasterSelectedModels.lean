import Hindman168.FiniteMasterSelectedModels
import Hindman168.SelectedChainIndices

/-! The simultaneously selected models work for every actual chain on
principal indices, with one fine padding preceding its first pivot. -/
namespace Hindman168
open FiniteMass Filter
universe u

theorem chain_master_selected_models (ι : Type*) [Fintype ι] (n s : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (M : ℕ) (hM : 0 < M), N ≤ M →
      ∀ (d : ℕ) (A : Finset ℚ) (D : Finset (MvPolynomial (Fin d) ℤ))
      (F : MasterParameterFamily), MasterParameterConditions M A D F →
      ∀ U : Ultrafilter ℕ,
      ∀ f : Finset ℕ → (i : ℕ) → ι → boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)),
      (∀ T i a w y, y ∈ (originalPivotMass F i w).support → 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < M) ∧
        (∀ j w, (masterGapIndex M hM (e j) w).val = e j) ∧
        ∃ t : (T : Finset (Fin n)) → (b : Fin n) → ι →
          boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F (energyPrincipal e b) w)),
          (∀ T b a,
            NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b)) (fun w y => (t T b a).val w y) ∧
            (∀ w y, 0 ≤ (t T b a).val w y ∧ (t T b a).val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (masterGapIndex M hM (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U (f (T.image (energyPrincipal e)) (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U (t T b a)‖ < ε ∧
            ∀ v : Fin n, v ≤ b → T.image (energyPrincipal e) ⊆ energyPrincipalSet e →
              (∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e v) →
              ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                  (masterGapIndex M hM (energyPadding e v))).starProjection
                  (hilbertFamilyToCompletion _ U (f (T.image (energyPrincipal e)) (energyPrincipal e b) a) -
                    hilbertFamilyToCompletion _ U (t T b a))‖ ≤ 2 * ε) ∧
          (∀ m : ℕ, ∀ C : Chain (m + 1),
            (∀ i, C.block i ⊆ energyPrincipalSet e) →
            ∃ p : Fin (m + 1) → Fin n,
              (∀ i, energyPrincipal e (p i) = C.pivot i) ∧
              (∀ i, ∀ y ∈ C.tail i, y < energyPadding e (p 0)) ∧
              ∀ i a,
                ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e (p i))) U
                    (masterGapIndex M hM (energyPadding e (p 0)))).starProjection
                    (hilbertFamilyToCompletion _ U (f (C.tail i) (energyPrincipal e (p i)) a) -
                      hilbertFamilyToCompletion _ U (t (principalTailPositions e (C.tail i)) (p i) a))‖ ≤ 2 * ε) ∧
          ∃ G : NativeNilmanifoldData.{u} s,
            letI := G.metric
            letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
            ∃ B : ℝ, ∃ Lip : NNReal, 0 ≤ B ∧ ∀ T b a,
              ∃ (obs : ℕ → (ℤ × ℤ) → C(G.G ⧸ G.Γ, ℝ))
                (g x : ℕ → (ℤ × ℤ) → G.G),
                (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
                (fun w y => (t T b a).val w y) = piecewiseLinearNilsequence G.Γ F
                  (masterGapIndex M hM (energyPadding e b)) obs g x := by
  classical
  obtain ⟨N, hN⟩ := finite_master_selected_models.{u} ι n s ε hε
  refine ⟨N, ?_⟩
  intro M hM hNM d A D F hF U f hf
  obtain ⟨e, heM, heval, t, ht, hG⟩ := hN M hM hNM d A D F hF U f hf
  refine ⟨e, heM, heval, t, ht, ?_, hG⟩
  intro m C hC
  obtain ⟨p, _, hp, htail⟩ := selected_chain_coordinates e C hC
  obtain ⟨hpi, hbefore, _⟩ := selected_chain_common_padding e C hC p hp
  refine ⟨p, hp, hbefore, ?_⟩
  intro i a
  have hsubset : C.tail i ⊆ energyPrincipalSet e :=
    fun _ hy => hC i (Finset.mem_insert_of_mem hy)
  have hfirst : ∀ y ∈ C.tail i, y < energyPrincipal e (p 0) := by
    intro y hy
    rw [hp 0]
    exact C.tails_before_pivots i 0 y hy
  have hh := (ht (principalTailPositions e (C.tail i)) (p i) a).2.2.2
    (p 0) (hpi i) (by rw [htail i]; exact hsubset) (by rw [htail i]; exact hfirst)
  simpa only [htail i] using hh

end Hindman168
