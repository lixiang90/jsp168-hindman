import Hindman168.VectorPolynomialMultivariateProjection

namespace Hindman168

abbrev RoughVectorMvPolynomial (σ E : Type*) := List (MvPolynomial σ ℝ × E)

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roughVectorMvEval (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) : E :=
  (p.map (fun a => MvPolynomial.eval x a.1 • a.2)).sum

def RoughVectorMvDegreeLE (p : RoughVectorMvPolynomial σ E) (d : ℕ) : Prop :=
  ∀ a ∈ p, a.1.totalDegree ≤ d

noncomputable def roughVectorMvScale (r : ℝ) (p : RoughVectorMvPolynomial σ E) :
    RoughVectorMvPolynomial σ E := p.map (fun a => (a.1, r • a.2))

noncomputable def roughVectorMvBilinear (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughVectorMvPolynomial σ E) : RoughVectorMvPolynomial σ E :=
  p.flatMap (fun a => q.map (fun b => (a.1 * b.1, B a.2 b.2)))

theorem roughVectorMvEval_append (p q : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (p ++ q) x = roughVectorMvEval p x + roughVectorMvEval q x := by
  simp only [roughVectorMvEval, List.map_append, List.sum_append]

theorem roughVectorMvEval_scale (r : ℝ) (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvScale r p) x = r • roughVectorMvEval p x := by
  induction p with
  | nil => simp [roughVectorMvScale, roughVectorMvEval]
  | cons a p ih =>
    change MvPolynomial.eval x a.1 • (r • a.2) +
      roughVectorMvEval (roughVectorMvScale r p) x =
        r • (MvPolynomial.eval x a.1 • a.2 + roughVectorMvEval p x)
    rw [ih, smul_add, smul_comm]

theorem roughVectorMvEval_bilinear (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughVectorMvBilinear B p q) x =
      B (roughVectorMvEval p x) (roughVectorMvEval q x) := by
  induction p with
  | nil => simp [roughVectorMvBilinear, roughVectorMvEval]
  | cons a p ih =>
    have hr : roughVectorMvEval (q.map (fun b => (a.1 * b.1, B a.2 b.2))) x =
        B (MvPolynomial.eval x a.1 • a.2) (roughVectorMvEval q x) := by
      clear ih
      induction q with
      | nil => simp [roughVectorMvEval]
      | cons b q hq =>
        change MvPolynomial.eval x (a.1 * b.1) • B a.2 b.2 +
          roughVectorMvEval (q.map (fun b => (a.1 * b.1, B a.2 b.2))) x =
            B (MvPolynomial.eval x a.1 • a.2)
              (MvPolynomial.eval x b.1 • b.2 + roughVectorMvEval q x)
        rw [hq]
        simp only [map_add, map_smul, smul_apply, map_mul, mul_smul]
        rw [smul_comm]
    change roughVectorMvEval (_ ++ roughVectorMvBilinear B p q) x = _
    rw [roughVectorMvEval_append, hr, ih]
    change _ = B (MvPolynomial.eval x a.1 • a.2 + roughVectorMvEval p x) _
    rw [map_add, add_apply]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem roughVectorMvDegreeLE_mono {p : RoughVectorMvPolynomial σ E} {d e : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (h : d ≤ e) : RoughVectorMvDegreeLE p e :=
  fun a ha => (hp a ha).trans h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem roughVectorMvDegreeLE_append {p q : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (hq : RoughVectorMvDegreeLE q d) :
    RoughVectorMvDegreeLE (p ++ q) d :=
  fun a ha => (List.mem_append.mp ha).elim (hp a) (hq a)

theorem roughVectorMvDegreeLE_scale (r : ℝ) {p : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hp : RoughVectorMvDegreeLE p d) : RoughVectorMvDegreeLE (roughVectorMvScale r p) d := by
  rintro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hp b hb

theorem roughVectorMvDegreeLE_bilinear (B : E →L[ℝ] (E →L[ℝ] E))
    {p q : RoughVectorMvPolynomial σ E} {d e : ℕ}
    (hp : RoughVectorMvDegreeLE p d) (hq : RoughVectorMvDegreeLE q e) :
    RoughVectorMvDegreeLE (roughVectorMvBilinear B p q) (d + e) := by
  rintro a ha
  obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  exact (MvPolynomial.totalDegree_mul b.1 c.1).trans (Nat.add_le_add (hp b hb) (hq c hc))

noncomputable def roughVectorMvProjection (ell : E →ₗ[ℝ] ℝ) :
    RoughVectorMvPolynomial σ E → MvPolynomial σ ℝ
  | [] => 0
  | a :: p => a.1 * MvPolynomial.C (ell a.2) + roughVectorMvProjection ell p

theorem roughVectorMvProjection_eval (ell : E →ₗ[ℝ] ℝ)
    (p : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    MvPolynomial.eval x (roughVectorMvProjection ell p) = ell (roughVectorMvEval p x) := by
  induction p with
  | nil => simp [roughVectorMvProjection, roughVectorMvEval]
  | cons a p ih =>
    change MvPolynomial.eval x (a.1 * MvPolynomial.C (ell a.2) + roughVectorMvProjection ell p) =
      ell (MvPolynomial.eval x a.1 • a.2 + roughVectorMvEval p x)
    simp only [map_add, map_mul, MvPolynomial.eval_C, ih, map_smul, smul_eq_mul]

theorem roughVectorMvProjection_degree (ell : E →ₗ[ℝ] ℝ)
    {p : RoughVectorMvPolynomial σ E} {d : ℕ} (hp : RoughVectorMvDegreeLE p d) :
    (roughVectorMvProjection ell p).totalDegree ≤ d := by
  induction p with
  | nil => simp [roughVectorMvProjection]
  | cons a p ih =>
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le _ (ih (fun b hb => hp b (List.mem_cons_of_mem _ hb)))
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using hp a List.mem_cons_self)

end Hindman168
