import Hindman168.FiniteOrderNativeShortCubeModels
import Hindman168.SelectedChainIndices
import Hindman168.NativeVaryingGapCommon

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- One finite family of actual native coarse models controls all chains
on the selected principal indices. The same J and pre-Ramsey thresholds for the whole finite dimension list
work at each chain's common fine padding. A common native manifold and
uniform observable bounds retain every model's own coarse partition. -/
theorem finite_order_native_chain_prediction (ι : Type*) [Fintype ι] (n s : ℕ)
    (Q : Type*) [Fintype Q] (dim : Q → ℕ)
    (hinverse : ∀ q, HasNativePeriodicIntervalInverse.{u} s (2 ^ dim q + 2 ^ dim q - 1))
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ ε : ℝ, 0 < κ ∧ 0 < ε ∧ 2 * ε < κ ∧
      ∃ N : ℕ, ∀ (M : ℕ) (hM : 0 < M), N ≤ M →
      ∀ (r : ℕ) (D : Finset (MvPolynomial (Fin r) ℤ)) (hD : ∀ p ∈ D, p ≠ 0),
      let F := constructedMasterFamily M D hD
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f : Finset ℕ → (i : ℕ) → ι →
          boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ T i a w y, 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1),
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < M) ∧
        ∃ t : (T : Finset (Fin n)) → (b : Fin n) → ι →
          boundedHilbertFamilies (fun w => FiniteMassL2
            (originalPivotMass F (energyPrincipal e b) w)),
          (∀ T b a,
            NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b))
              (fun w y => (t T b a).val w y) ∧
            (∀ w y, 0 ≤ (t T b a).val w y ∧ (t T b a).val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (masterGapIndex M hM (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U
                  (f (T.image (energyPrincipal e)) (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U (t T b a)‖ < ε) ∧
          (∀ m : ℕ, ∀ C : Chain (m + 1),
            (∀ i, C.block i ⊆ energyPrincipalSet e) →
            ∃ p : Fin (m + 1) → Fin n, StrictMono p ∧
              (∀ i, energyPrincipal e (p i) = C.pivot i) ∧
              (∀ i, ∀ y ∈ C.tail i, y < energyPadding e (p 0)) ∧
              ∀ i a (q : Q) (pol : MvPolynomial (Fin r) ℤ), pol ∈ D →
                ∀ (P : Finset (MvPolynomial (Fin r) ℤ)), (∀ q ∈ P, q ≠ 0) → pol ∈ P →
                ∀ᶠ w in (U : Filter ℕ),
                  let μ := conditionMass (dyadicPoolTupleMass
                    (fun _ : Fin r => F.pool w (energyPadding e (p 0)))) (primeSampleGood P)
                  expectation μ (fun x => |integerPredictionShortCubeStatistic w
                    (F.modulus w : ℕ) (F.gap w (energyPadding e (p 0)))
                    (F.cutoff w (energyPrincipal e (p i))) (dim q) J pol
                    (fun y => (f (C.tail i) (energyPrincipal e (p i)) a).val w y -
                      (t (principalTailPositions e (C.tail i)) (p i) a).val w y) x|) < η) ∧
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
  obtain ⟨J, hJ, κ, ε, hκ, hε, hsmall, N, hN⟩ :=
    finite_order_native_shortCube_models.{u} ι n s Q dim hinverse η hη
  refine ⟨J, hJ, κ, ε, hκ, hε, hsmall, N, ?_⟩
  intro M hM hNM r D hD F U hU f hf
  obtain ⟨e, heM, he⟩ := hN M hM hNM r D hD U hU f hf
  have hchoose := fun (T : Finset (Fin n)) b a => he (T.image (energyPrincipal e)) b a
  choose t ht using hchoose
  refine ⟨e, heM, t, ?_, ?_, ?_⟩
  · intro T b a
    exact ⟨(ht T b a).1, (ht T b a).2.1, (ht T b a).2.2.1⟩
  · intro m C hC
    obtain ⟨p, hpmono, hp, htail⟩ := selected_chain_coordinates e C hC
    obtain ⟨hpi, hbefore, _⟩ := selected_chain_common_padding e C hC p hp
    refine ⟨p, hpmono, hp, hbefore, ?_⟩
    intro i a q pol hpol P hP hpolP
    have hsubset : C.tail i ⊆ energyPrincipalSet e :=
      fun _ hy => hC i (Finset.mem_insert_of_mem hy)
    have hfirst : ∀ y ∈ C.tail i, y < energyPrincipal e (p 0) := by
      intro y hy
      rw [hp 0]
      exact C.tails_before_pivots i 0 y hy
    have hh := ((ht (principalTailPositions e (C.tail i)) (p i) a).2.2.2
      (p 0) (hpi i) (by rw [htail i]; exact hsubset)
      (by rw [htail i]; exact hfirst)).2 q pol hpol P hP hpolP
    simpa only [htail i] using hh
  · let labels := Finset (Fin n) × Fin n × ι
    let gaps : labels → ℕ → Fin M := fun q => masterGapIndex M hM (energyPadding e q.2.1)
    let values : labels → ℕ → ℤ → ℝ := fun q w y => (t q.1 q.2.1 q.2.2).val w y
    obtain ⟨G, hG⟩ := nativeVaryingGap_common_uniform (s := s) F gaps values
      (fun q => (ht q.1 q.2.1 q.2.2).1)
    refine ⟨G, ?_⟩
    letI := G.metric
    letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
    obtain ⟨B, Lip, hB, hrep⟩ := hG
    exact ⟨B, Lip, hB, fun T b a => hrep (T, b, a)⟩

end Hindman168
