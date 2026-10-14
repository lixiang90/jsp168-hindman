import Hindman168.RoughTranslationTopCoefficients
import Hindman168.RoughVectorWeightedDegree

namespace Hindman168
open scoped Classical
variable {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvDifference (h : κ → ℝ) (p : RoughVectorMvPolynomial κ E) :
    RoughVectorMvPolynomial κ E :=
  p.filterMap (fun a => if roughMvAffineSubstitution h (fun _ => 1) a.1-a.1 = 0 then none
    else some (roughMvAffineSubstitution h (fun _ => 1) a.1-a.1, a.2))

omit [Fintype κ] in
theorem rough_vector_difference_eval (h x : κ → ℝ) (p : RoughVectorMvPolynomial κ E) :
    roughVectorMvEval (roughVectorMvDifference h p) x =
      roughVectorMvEval p (fun j => x j+h j)-roughVectorMvEval p x := by
  induction p with
  | nil => simp [roughVectorMvDifference, roughVectorMvEval]
  | cons a p ih =>
      have he : MvPolynomial.eval x (roughMvAffineSubstitution h (fun _ => 1) a.1-a.1) =
          MvPolynomial.eval (fun j => x j+h j) a.1-MvPolynomial.eval x a.1 := by
        rw [map_sub, roughMvAffineSubstitution_eval]
        simp only [one_mul, add_comm]
      by_cases hz : roughMvAffineSubstitution h (fun _ => 1) a.1-a.1 = 0
      · have he0 : MvPolynomial.eval (fun j => x j+h j) a.1 = MvPolynomial.eval x a.1 := by
          rw [hz, map_zero] at he
          exact sub_eq_zero.mp he.symm
        simp only [roughVectorMvDifference, if_pos hz, List.filterMap,
          roughVectorMvEval, List.map_cons, List.sum_cons] at ⊢
        change roughVectorMvEval (roughVectorMvDifference h p) x = _
        rw [ih, he0]
        abel
      · simp only [roughVectorMvDifference, List.filterMap_cons, if_neg hz]
        change roughVectorMvEval ((roughMvAffineSubstitution h (fun _ => 1) a.1-a.1, a.2) ::
            roughVectorMvDifference h p) x = _
        change MvPolynomial.eval x (roughMvAffineSubstitution h (fun _ => 1) a.1-a.1) • a.2 +
          roughVectorMvEval (roughVectorMvDifference h p) x =
          (MvPolynomial.eval (fun j => x j+h j) a.1 • a.2+roughVectorMvEval p (fun j => x j+h j))-
            (MvPolynomial.eval x a.1 • a.2+roughVectorMvEval p x)
        rw [he, sub_smul, ih]
        abel

omit [Fintype κ] in
theorem rough_vector_weighted_affine (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (u v : κ → ℝ) {p : RoughVectorMvPolynomial κ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvAffineSubstitution u v p) k := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hF (Nat.add_le_add_right (roughMvAffineSubstitution_degree u v b.1) k) (hp b hb)

theorem rough_vector_weighted_difference (F : ℕ → Submodule ℝ E) (hF : Antitone F)
    (h : κ → ℝ) {p : RoughVectorMvPolynomial κ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree F p k) :
    RoughVectorMvWeightedDegree F (roughVectorMvDifference h p) (k+1) := by
  rintro a ha
  obtain ⟨b, hb, hval⟩ := List.mem_filterMap.mp ha
  split_ifs at hval with hz
  have he := Option.some.inj hval
  subst a
  have hd := rough_translation_difference_degree h b.1 hz
  exact hF (by dsimp; omega) (hp b hb)

end Hindman168
