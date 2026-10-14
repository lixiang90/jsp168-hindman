import Hindman168.FiniteVectorPolynomialSums

/-! Rational coefficient propagation through two distinct original
subspaces. A bilinear operation can improve the layer of its second
input. Finite coefficient proofs require no topological closedness. -/

namespace Hindman168
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialCoefficientsMem_mono {V W : Submodule ℚ E}
    (hVW : V ≤ W) {p : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p) :
    finiteVectorPolynomialCoefficientsMem W p := fun a ha => hVW (hp a ha)

theorem finiteVectorPolynomialCoefficientsMem_bilinear_mixed
    (V F N : Submodule ℚ E) (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ v ∈ V, ∀ w ∈ F, B v w ∈ N)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem F q) :
    finiteVectorPolynomialCoefficientsMem N (finiteVectorPolynomialBilinear B p q) := by
  intro z hz
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hz
  obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hb
  exact hB a.2 (hp a ha) b.2 (hq b hbmem)

theorem finiteVectorPolynomialCoefficientsMem_adPower_positive_mixed
    (V F N : Submodule ℚ E) (hNF : N ≤ F)
    (B : E →L[ℝ] (E →L[ℝ] E))
    (hB : ∀ v ∈ V, ∀ w ∈ F, B v w ∈ N)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem F q) (n : ℕ) :
    finiteVectorPolynomialCoefficientsMem N (finiteVectorPolynomialAdPower B p q (n + 1)) := by
  induction n with
  | zero =>
    exact finiteVectorPolynomialCoefficientsMem_bilinear_mixed V F N B hB hp hq
  | succ n ih =>
    exact finiteVectorPolynomialCoefficientsMem_bilinear_mixed V F N B hB hp
      (finiteVectorPolynomialCoefficientsMem_mono hNF ih)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E] in
 theorem finiteVectorPolynomialSum_zero_split (n : ℕ) (P : ℕ → List (ℕ × E)) :
    finiteVectorPolynomialSum (n + 1) P =
      P 0 ++ finiteVectorPolynomialSum n (fun j => P (j + 1)) := by
  induction n with
  | zero => simp [finiteVectorPolynomialSum]
  | succ n ih =>
    rw [finiteVectorPolynomialSum_succ, ih, finiteVectorPolynomialSum_succ]
    rw [List.append_assoc]

omit [NormedSpace ℝ E] in
 theorem finiteVectorPolynomialPrimitive_append (p q : List (ℕ × E)) :
    finiteVectorPolynomialPrimitive (p ++ q) =
      finiteVectorPolynomialPrimitive p ++ finiteVectorPolynomialPrimitive q := by
  exact List.map_append

 theorem finiteVectorPolynomialEval_primitive_constant (v : E) (t : ℝ) :
    finiteVectorPolynomialEval (finiteVectorPolynomialPrimitive [(0, v)]) t = t • v := by
  simp only [finiteVectorPolynomialPrimitive, List.map_cons, List.map_nil,
    Nat.cast_zero, zero_add, inv_one, one_smul, finiteVectorPolynomialEval_singleton,
    pow_one]

end Hindman168
