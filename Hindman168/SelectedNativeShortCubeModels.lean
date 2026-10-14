import Hindman168.MasterModelDifferenceShortCube
import Hindman168.ConcreteMasterSelectedModels

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Topology Classical
universe u

/-- Energy selection and the conditional inverse estimate are used in the
paper's order: J, the positive projection threshold and the coarse error
are fixed before N. The chosen coarse model then works at every permissible
earlier selected padding, with the original short-cube and prime laws. -/
theorem selected_native_shortCube_models (ι : Type*) [Fintype ι] (n s d : ℕ)
    (hinverse : HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
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
        ∀ T : Finset ℕ, ∀ b : Fin n, ∀ a : ι,
          ∃ t : boundedHilbertFamilies
              (fun w => FiniteMassL2 (originalPivotMass F (energyPrincipal e b) w)),
            NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b))
              (fun w y => t.val w y) ∧
            (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (masterGapIndex M hM (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U t‖ < ε ∧
            ∀ v : Fin n, v ≤ b → T ⊆ energyPrincipalSet e →
              (∀ y ∈ T, y < energyPrincipal e v) →
              ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                  (masterGapIndex M hM (energyPadding e v))).starProjection
                  (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a) -
                    hilbertFamilyToCompletion _ U t)‖ ≤ 2 * ε ∧
              ∀ (pol : MvPolynomial (Fin r) ℤ), pol ∈ D →
                ∀ (P : Finset (MvPolynomial (Fin r) ℤ)), (∀ p ∈ P, p ≠ 0) → pol ∈ P →
                ∀ᶠ w in (U : Filter ℕ),
                  let μ := conditionMass (dyadicPoolTupleMass
                    (fun _ : Fin r => F.pool w (energyPadding e v))) (primeSampleGood P)
                  expectation μ (fun x => |integerPredictionShortCubeStatistic w
                    (F.modulus w : ℕ) (F.gap w (energyPadding e v))
                    (F.cutoff w (energyPrincipal e b)) d J pol
                    (fun y => (f T (energyPrincipal e b) a).val w y - t.val w y) x|) < η := by
  obtain ⟨J, hJ, κ, hκ, hshort⟩ := master_model_difference_shortCube_threshold s d hinverse η hη
  let ε := κ / 4
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hsmall : 2 * ε < κ := by dsimp only [ε]; linarith
  obtain ⟨N, hN⟩ := concrete_master_selected_models.{u} ι n s ε hε
  refine ⟨J, hJ, κ, ε, hκ, hε, hsmall, N, ?_⟩
  intro M hM hNM r D hD F U hU f hf
  let hF := constructedMasterFamily_conditions M ∅ (by simp) D hD
  obtain ⟨e, heM, _, he⟩ := hN M hM hNM r ∅ D F hF U f
    (fun T i a w y _ => hf T i a w y)
  refine ⟨e, heM, ?_⟩
  intro T b a
  obtain ⟨t, ht, hb, ha, hproj⟩ := he T b a
  refine ⟨t, ht, hb, ha, ?_⟩
  intro v hvb hT hbefore
  have hp := hproj v hvb hT hbefore
  refine ⟨hp, ?_⟩
  intro pol hpol P hP hpolP
  have hl : energyPadding e v < M := heM ⟨2 * v.val, by omega⟩
  have hi : energyPrincipal e b < M := heM ⟨2 * b.val + 1, by omega⟩
  have hli : energyPadding e v ≤ energyPrincipal e b :=
    (energyPadding_mono e hvb).trans (energyPadding_lt_principal e b).le
  exact hshort hM D hD pol hpol P hP hpolP
    (energyPadding e v) (energyPrincipal e b) hl hi hli U hU
    (f T (energyPrincipal e b) a) t (hf T (energyPrincipal e b) a) hb (hp.trans_lt hsmall)

end Hindman168
