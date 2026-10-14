import Hindman168.ConcreteMasterSelectedModels
import Hindman168.NativeVaryingGapCommon

/-! Simultaneous finite selected models with a common actual native space.
Tails are indexed by all subsets of the finite principal index type. -/
namespace Hindman168
open FiniteMass Filter
universe u

theorem finite_master_selected_models (ι : Type*) [Fintype ι] (n s : ℕ)
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
  obtain ⟨N, hN⟩ := concrete_master_selected_models.{u} ι n s ε hε
  refine ⟨N, ?_⟩
  intro M hM hNM d A D F hF U f hf
  obtain ⟨e, heM, heval, he⟩ := hN M hM hNM d A D F hF U f hf
  have hchoose := fun (T : Finset (Fin n)) b a => he (T.image (energyPrincipal e)) b a
  choose t ht using hchoose
  let κ := Finset (Fin n) × Fin n × ι
  let gaps : κ → ℕ → Fin M := fun q => masterGapIndex M hM (energyPadding e q.2.1)
  let values : κ → ℕ → ℤ → ℝ := fun q w y => (t q.1 q.2.1 q.2.2).val w y
  obtain ⟨G, hG⟩ := nativeVaryingGap_common_uniform (s := s) F gaps values
    (fun q => (ht q.1 q.2.1 q.2.2).1)
  refine ⟨e, heM, heval, t, ht, G, ?_⟩
  letI := G.metric
  letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨B, Lip, hB, hrep⟩ := hG
  exact ⟨B, Lip, hB, fun T b a => hrep (T,b,a)⟩

end Hindman168
