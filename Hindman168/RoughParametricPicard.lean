import Hindman168.RoughParametricDegree

namespace Hindman168

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughParametricDefect (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p q : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  roughParametricSum s (fun n =>
    roughParametricScale (-((-1 : ℚ) ^ (n + 1) / ((n + 2).factorial : ℚ)))
      (roughParametricAd B p q (n + 1)))

noncomputable def roughParametricDefectPower (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p q : RoughParametricCurve σ E) : ℕ → RoughParametricCurve σ E
  | 0 => q
  | n + 1 => roughParametricDefect B s p (roughParametricDefectPower B s p q n)

noncomputable def roughParametricField (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (p q : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  roughParametricSum s (roughParametricDefectPower B s p q)

noncomputable def roughParametricPicard (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    (w u : RoughVectorMvPolynomial σ E) : ℕ → RoughParametricCurve σ E
  | 0 => [(0,u)]
  | n + 1 => [(0,u)] ++ roughParametricPrimitive
      (roughParametricField B s (roughParametricPicard B s w u n) [(0,w)])

theorem roughParametricDefect_degree (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    {p q : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q e) :
    RoughParametricDegreeLE (roughParametricDefect B s p q) (s * d + e) := by
  apply roughParametricDegreeLE_sum
  intro n hn
  apply roughParametricDegreeLE_scale
  exact roughParametricDegreeLE_mono (roughParametricDegreeLE_ad B hp hq (n+1))
    (Nat.add_le_add_right (Nat.mul_le_mul_right d (by omega)) e)

theorem roughParametricDefectPower_degree (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    {p q : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q e) (n : ℕ) :
    RoughParametricDegreeLE (roughParametricDefectPower B s p q n) (n * (s * d) + e) := by
  induction n with
  | zero => simpa only [roughParametricDefectPower, zero_mul, zero_add] using hq
  | succ n ih =>
    simpa only [roughParametricDefectPower, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm] using
      roughParametricDefect_degree B s hp ih

theorem roughParametricField_degree (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    {p q : RoughParametricCurve σ E} {d e : ℕ}
    (hp : RoughParametricDegreeLE p d) (hq : RoughParametricDegreeLE q e) :
    RoughParametricDegreeLE (roughParametricField B s p q) (s * (s * d) + e) := by
  apply roughParametricDegreeLE_sum
  intro n hn
  exact roughParametricDegreeLE_mono (roughParametricDefectPower_degree B s hp hq n)
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_of_lt hn)) e)

theorem roughParametricPicard_degree (B : E →L[ℝ] (E →L[ℝ] E)) (s : ℕ)
    {w u : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hw : RoughVectorMvDegreeLE w d) (hu : RoughVectorMvDegreeLE u d) (n : ℕ) :
    RoughParametricDegreeLE (roughParametricPicard B s w u n) ((s * s + 1)^n * d) := by
  induction n with
  | zero => simpa only [roughParametricPicard, pow_zero, one_mul] using
      roughParametricDegreeLE_singleton hu 0
  | succ n ih =>
    have hpow : 1 ≤ (s*s+1)^n := Nat.one_le_pow n _ (by omega)
    have hd : d ≤ (s*s+1)^n*d := by nlinarith
    apply roughParametricDegreeLE_append
    · exact roughParametricDegreeLE_singleton (roughVectorMvDegreeLE_mono hu (by
        rw [pow_succ]; nlinarith)) 0
    · apply roughParametricDegreeLE_primitive
      exact roughParametricDegreeLE_mono
        (roughParametricField_degree B s ih (roughParametricDegreeLE_singleton hw 0)) (by
          rw [pow_succ]; nlinarith)

end Hindman168
