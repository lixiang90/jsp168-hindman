import Hindman168.FiniteVectorPolynomialBilinear
import Hindman168.FiniteVectorPolynomialIntegral

/-! Finite coefficient membership in an actual Q-linear subspace is
preserved by exact polynomial operations. Bilinear closure is required
only of the original coefficient structure; integration uses explicit
rational coefficient division, never topological closedness. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

def finiteVectorPolynomialCoefficientsMem (V : Submodule ℚ E) (p : List (ℕ × E)) : Prop :=
  ∀ a ∈ p, a.2 ∈ V

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_singleton (V : Submodule ℚ E)
    (n : ℕ) {v : E} (hv : v ∈ V) : finiteVectorPolynomialCoefficientsMem V [(n, v)] := by
  intro a ha
  have he : a = (n, v) := List.mem_singleton.mp ha
  rw [he]
  exact hv

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_nil (V : Submodule ℚ E) :
    finiteVectorPolynomialCoefficientsMem V [] := by
  intro a ha
  simp only [List.not_mem_nil] at ha

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_append (V : Submodule ℚ E)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) :
    finiteVectorPolynomialCoefficientsMem V (p ++ q) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · exact hq a ha

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_scale (V : Submodule ℚ E)
    {p : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p) (r : ℚ) :
    finiteVectorPolynomialCoefficientsMem V (finiteVectorPolynomialScale r p) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact V.smul_mem r (hp a ha)

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_primitive (V : Submodule ℚ E)
    {p : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p) :
    finiteVectorPolynomialCoefficientsMem V (finiteVectorPolynomialPrimitive p) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact V.smul_mem _ (hp a ha)

 theorem finiteVectorPolynomialCoefficientsMem_bilinear (V : Submodule ℚ E)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ v ∈ V, ∀ w ∈ V, B v w ∈ V)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem V q) :
    finiteVectorPolynomialCoefficientsMem V (finiteVectorPolynomialBilinear B p q) := by
  intro z hz
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hz
  obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hb
  exact hB a.2 (hp a ha) b.2 (hq b hbmem)

 theorem finiteVectorPolynomialEval_rational_mem (V : Submodule ℚ E)
    {p : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p) (q : ℚ) :
    finiteVectorPolynomialEval p (q : ℝ) ∈ V := by
  induction p with
  | nil => exact V.zero_mem
  | cons a p ih =>
    have ha : a.2 ∈ V := hp a (List.mem_cons_self)
    have ht : finiteVectorPolynomialCoefficientsMem V p :=
      fun b hb => hp b (List.mem_cons_of_mem a hb)
    change (q : ℝ) ^ a.1 • a.2 + finiteVectorPolynomialEval p (q : ℝ) ∈ V
    apply V.add_mem _ (ih ht)
    have he : (q : ℝ) ^ a.1 • a.2 = (q ^ a.1 : ℚ) • a.2 := by
      rw [← Rat.cast_pow, Rat.cast_smul_eq_qsmul]
    rw [he]
    exact V.smul_mem _ ha

omit [Module ℚ E] in
 theorem finiteVectorPolynomialEval_flatten (ps : List (List (ℕ × E))) (t : ℝ) :
    finiteVectorPolynomialEval ps.flatten t =
      (ps.map (fun p => finiteVectorPolynomialEval p t)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.flatten_cons, finiteVectorPolynomialEval_append, ih]
    rfl

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_flatten (V : Submodule ℚ E)
    {ps : List (List (ℕ × E))} (h : ∀ p ∈ ps, finiteVectorPolynomialCoefficientsMem V p) :
    finiteVectorPolynomialCoefficientsMem V ps.flatten := by
  intro a ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatten.mp ha
  exact h p hp a ha

end Hindman168
