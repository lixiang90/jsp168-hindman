import Hindman168.LeibmanDenseDirectionReconstruction
import Hindman168.ModOneNaturalMultiplier

namespace Hindman168
open scoped BigOperators Classical

theorem leibman_simultaneous_direction_coefficient_bound {ρ : Type*} [Fintype ρ] {n : ℕ}
    (I : ρ → Finset (Fin n → ℕ)) (d : ℕ)
    (hd : ∀ r, ∀ i ∈ I r, (∑ j, i j) ≤ d) (L : ℕ) (hL : 0 < L) :
    ∃ C : ℕ, 0 < C ∧ ∀ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) → d*L^n < T.card*L →
      ∃ M : ℕ, 0 < M ∧ M ≤ C ∧ ∀ r (a : ↥(I r) → ℝ) (eps : ℝ), 0 ≤ eps →
        (∀ t : ↥T, ‖((∑ j : ↥(I r), a j*
          leibmanMonomialVector (I r) (fun k => (t.val k : ℝ)) j : ℝ) : UnitAddCircle)‖ ≤ eps) →
        ∀ i, ‖(((M : ℝ)*a i : ℝ) : UnitAddCircle)‖ ≤ (C : ℝ)*eps := by
  have hdata : ∀ r, ∃ B : ℕ, 0 < B ∧ ∀ T : Finset (Fin n → ℕ),
      T ⊆ Fintype.piFinset (fun _ : Fin n => Finset.range L) → d*L^n < T.card*L →
      ∃ D : ℕ, 0 < D ∧ D ≤ B ∧ ∀ (a : ↥(I r) → ℝ) (eps : ℝ), 0 ≤ eps →
        (∀ t : ↥T, ‖((∑ j : ↥(I r), a j*
          leibmanMonomialVector (I r) (fun k => (t.val k : ℝ)) j : ℝ) : UnitAddCircle)‖ ≤ eps) →
        ∀ i, ‖(((D : ℝ)*a i : ℝ) : UnitAddCircle)‖ ≤ (B : ℝ)*eps :=
    fun r => leibman_dense_direction_modular_coefficient_bound (I r) d (hd r) L hL
  choose b hb hstep using hdata
  let B := 1 + ∑ r, b r
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hbB (r : ρ) : b r ≤ B :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)).trans
      (by dsimp only [B]; omega)
  let C := B^(Fintype.card ρ+1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T hT hdense
  have hex := fun r => hstep r T hT hdense
  choose D hD hDb hcoeff using hex
  obtain ⟨M, hM, hMC, hmult⟩ := finite_mod_one_common_multiplier D B hB hD
    (fun r => (hDb r).trans (hbB r))
  refine ⟨M, hM, hMC, ?_⟩
  intro r a eps heps hvalues i
  apply hmult r (a i) eps heps
  exact (hcoeff r a eps heps hvalues i).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hbB r) heps)

end Hindman168
