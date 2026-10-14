import Hindman168.RoughInterpolationUniformError

namespace Hindman168
open Polynomial
open scoped BigOperators Classical

noncomputable def roughRationalInterpolation (q H : ℕ) (values : Fin (q + 1) → ℤ) : ℚ[X] :=
  Lagrange.interpolate Finset.univ (fun i => (roughInterpolationNode q H i : ℚ))
    (fun i => (values i : ℚ))

theorem roughRationalInterpolation_degree {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (values : Fin (q + 1) → ℤ) : (roughRationalInterpolation q H values).natDegree ≤ q := by
  apply natDegree_le_of_degree_le
  have hinj : Set.InjOn (fun i => (roughInterpolationNode q H i : ℚ))
      (Finset.univ : Finset (Fin (q + 1))) := by
    intro i _ j _ he
    apply roughInterpolationNode_injective hq hH
    change (roughInterpolationNode q H i : ℚ) = (roughInterpolationNode q H j : ℚ) at he
    exact_mod_cast he
  simpa only [roughRationalInterpolation, Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] using
    Lagrange.degree_interpolate_le (fun i => (values i : ℚ)) hinj

theorem roughRationalInterpolation_eval_node {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (values : Fin (q + 1) → ℤ) (i : Fin (q + 1)) :
    (roughRationalInterpolation q H values).eval (roughInterpolationNode q H i : ℚ) = values i := by
  apply Lagrange.eval_interpolate_at_node _ _ (Finset.mem_univ i)
  intro j _ k _ he
  apply roughInterpolationNode_injective hq hH
  change (roughInterpolationNode q H j : ℚ) = (roughInterpolationNode q H k : ℚ) at he
  exact_mod_cast he

theorem roughRationalInterpolation_map_real {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H)
    (values : Fin (q + 1) → ℤ) :
    (roughRationalInterpolation q H values).map (Rat.castHom ℝ) =
      roughScaledInterpolation q (roughInterpolationStep q H) (fun i => (values i : ℝ)) := by
  have hdeg : ((roughRationalInterpolation q H values).map (Rat.castHom ℝ)).natDegree ≤ q :=
    natDegree_map_le.trans (roughRationalInterpolation_degree hq hH values)
  have hnode (i : Fin (q + 1)) :
      ((roughRationalInterpolation q H values).map (Rat.castHom ℝ)).eval
        ((i.val : ℝ) * roughInterpolationStep q H) = (values i : ℝ) := by
    have he : (i.val : ℝ) * roughInterpolationStep q H =
        (Rat.castHom ℝ) (roughInterpolationNode q H i : ℚ) := by
      change _ = ((roughInterpolationNode q H i : ℚ) : ℝ)
      simp only [roughInterpolationNode, Nat.cast_mul, Rat.cast_mul, Rat.cast_natCast]
    rw [he, eval_map_apply, roughRationalInterpolation_eval_node hq hH]
    change ((values i : ℚ) : ℝ) = (values i : ℝ)
    exact Rat.cast_intCast _
  have hr := roughScaledInterpolation_reproduce q (roughInterpolationStep q H)
    (by exact_mod_cast (roughInterpolationStep_pos hq hH).ne')
    ((roughRationalInterpolation q H values).map (Rat.castHom ℝ)) hdeg
  simp_rw [hnode] at hr
  exact hr.symm

theorem roughRationalInterpolation_fixed_integer_model {q H : ℕ} (hq : 0 < q) (hH : 2 * q + 2 ≤ H) :
    ∃ D : ℕ, 0 < D ∧ ∀ values : Fin (q + 1) → ℤ, ∃ P : ℤ[X],
      C (D : ℚ) * roughRationalInterpolation q H values = P.map (Int.castRingHom ℚ) ∧
      P.natDegree ≤ q := by
  obtain ⟨D, hD, hd⟩ := rough_interpolation_fixed_denominator
    (fun i : Fin (q + 1) => (roughInterpolationNode q H i : ℤ))
  refine ⟨D, hD, ?_⟩
  intro values
  obtain ⟨P, hp⟩ := hd values
  have hdec : (fun a b : Fin (q + 1) => Classical.propDecidable (a = b)) =
      instDecidableEqFin (q + 1) := Subsingleton.elim _ _
  rw [hdec] at hp
  have hclear : C (D : ℚ) * roughRationalInterpolation q H values = P.map (Int.castRingHom ℚ) := by
    simpa only [roughRationalInterpolation, Int.cast_natCast] using hp
  refine ⟨P, hclear, ?_⟩
  have hn : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  calc
    P.natDegree = (P.map (Int.castRingHom ℚ)).natDegree :=
      (natDegree_map_eq_of_injective (by
        intro a b h
        change (a : ℚ) = (b : ℚ) at h
        exact Int.cast_injective h) P).symm
    _ = (roughRationalInterpolation q H values).natDegree := by rw [← hclear, natDegree_C_mul hn]
    _ ≤ q := roughRationalInterpolation_degree hq hH values

end Hindman168
