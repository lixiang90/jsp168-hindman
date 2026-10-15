import Hindman168.OriginalBoundedNativeModelsNonempty
import Hindman168.OriginalSameStepLinearizationNative

/-! A finite list of genuine native linear models for all bounded niltests.
The list and its common Lipschitz constant are chosen before the source
nilmanifold, polynomial coefficients, or any sampling interval. -/

namespace Hindman168.OriginalBoundedNativeModels

open Module OAI.Erdos3
open scoped TensorProduct NNReal

/-- Finite-model normalization followed by same-step linearization. Every
integer evaluation is preserved, and a single constant bounds the actual
observable on each specified native quotient metric. -/
theorem exists_finite_native_linear_menu (s : ℕ) (hs : 1 ≤ s)
    {p : ℝ} (hp : 0 ≤ p) :
    ∃ n : ℕ, 0 < n ∧ ∃ models : Fin n → NativeNilmanifoldData.{0} s,
      ∃ K : ℝ≥0, 0 < K ∧
        ∀ (A : RationalGeometry s) (T : A.model.Niltest (fun _ : Unit => 1)),
          T.ComplexityLE p → T.normBound ≤ 1 →
          ∃ i : Fin n,
            letI := (models i).metric
            ∃ (obs : C((models i).G ⧸ (models i).Γ, ℂ)) (g x : (models i).G),
              (∀ y, ‖obs y‖ ≤ 1) ∧ LipschitzWith K obs ∧
                ∀ k : ℤ, obs (QuotientGroup.mk (g ^ k * x)) = T.eval (fun _ => k) := by
  classical
  letI := menuIndex_nonempty s hp
  choose models constants hmodels using
    (fun i : MenuIndex s p =>
      OriginalSameStepLinearization.exists_fixed_native_linearization (menuModel s p i) hs)
  let K : ℝ≥0 := 1 + Finset.univ.sup (fun i : MenuIndex s p =>
    constants i * menuLipschitzBound s p i)
  have hK (i : MenuIndex s p) : constants i * menuLipschitzBound s p i ≤ K := by
    exact (Finset.le_sup (f := fun j => constants j * menuLipschitzBound s p j)
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left (by positivity))
  let n := Fintype.card (MenuIndex s p)
  let e : Fin n ≃ MenuIndex s p := (Fintype.equivFin (MenuIndex s p)).symm
  refine ⟨n, Fintype.card_pos, fun i => models (e i), K, ?_, ?_⟩
  · dsimp [K]
    positivity
  · intro A T hcomplex hnorm
    obtain ⟨i, U, hUnorm, hUlip, hUeval⟩ := exists_menu_niltest A.model hp T hcomplex
    obtain ⟨j, rfl⟩ := e.surjective i
    letI := (models (e j)).metric
    have hnormU : U.normBound ≤ 1 := hUnorm.trans_le hnorm
    obtain ⟨obs, g, x, hn, hl, he⟩ := hmodels (e j) U hnormU
    refine ⟨j, obs, g, x, hn, ?_, ?_⟩
    · exact hl.weaken ((mul_le_mul_left' hUlip _).trans (hK (e j)))
    · intro k
      exact (he k).trans (hUeval (fun _ => k))

end Hindman168.OriginalBoundedNativeModels
