import Hindman168.RoughVectorMvPolynomial
import Hindman168.NativeLieRationalProductCurve

namespace Hindman168

abbrev RoughParametricCurve (σ E : Type*) := List (ℕ × RoughVectorMvPolynomial σ E)

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]

noncomputable def roughParametricSpecialize (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    List (ℕ × E) := p.map (fun a => (a.1, roughVectorMvEval a.2 x))

noncomputable def roughParametricScale (r : ℚ) (p : RoughParametricCurve σ E) :
    RoughParametricCurve σ E := p.map (fun a => (a.1, roughVectorMvScale (r : ℝ) a.2))

noncomputable def roughParametricPrimitive (p : RoughParametricCurve σ E) :
    RoughParametricCurve σ E :=
  p.map (fun a => (a.1 + 1, roughVectorMvScale (((a.1 + 1 : ℚ)⁻¹ : ℚ) : ℝ) a.2))

noncomputable def roughParametricBilinear (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughParametricCurve σ E) : RoughParametricCurve σ E :=
  p.flatMap (fun a => q.map (fun b => (a.1 + b.1, roughVectorMvBilinear B a.2 b.2)))

noncomputable def roughParametricAd (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughParametricCurve σ E) : ℕ → RoughParametricCurve σ E
  | 0 => q
  | n + 1 => roughParametricBilinear B p (roughParametricAd B p q n)

noncomputable def roughParametricSum (n : ℕ) (p : ℕ → RoughParametricCurve σ E) :
    RoughParametricCurve σ E := ((List.range n).map p).flatten

noncomputable def roughParametricEndpoint (p : RoughParametricCurve σ E) :
    RoughVectorMvPolynomial σ E := (p.map Prod.snd).flatten

theorem roughParametricSpecialize_scale (r : ℚ) (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize (roughParametricScale r p) x =
      finiteVectorPolynomialScale r (roughParametricSpecialize p x) := by
  simp only [roughParametricSpecialize, roughParametricScale, finiteVectorPolynomialScale,
    List.map_map, Function.comp_def, roughVectorMvEval_scale, Rat.cast_smul_eq_qsmul]

theorem roughParametricSpecialize_primitive (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize (roughParametricPrimitive p) x =
      finiteVectorPolynomialPrimitive (roughParametricSpecialize p x) := by
  simp only [roughParametricSpecialize, roughParametricPrimitive, finiteVectorPolynomialPrimitive,
    List.map_map, Function.comp_def, roughVectorMvEval_scale, Rat.cast_smul_eq_qsmul]

omit [Module ℚ E] in
theorem roughParametricSpecialize_bilinear (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize (roughParametricBilinear B p q) x =
      finiteVectorPolynomialBilinear B (roughParametricSpecialize p x) (roughParametricSpecialize q x) := by
  simp only [roughParametricSpecialize, roughParametricBilinear, finiteVectorPolynomialBilinear,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def, roughVectorMvEval_bilinear]

omit [Module ℚ E] in
theorem roughParametricSpecialize_ad (B : E →L[ℝ] (E →L[ℝ] E))
    (p q : RoughParametricCurve σ E) (n : ℕ) (x : σ → ℝ) :
    roughParametricSpecialize (roughParametricAd B p q n) x =
      finiteVectorPolynomialAdPower B (roughParametricSpecialize p x) (roughParametricSpecialize q x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [roughParametricAd, roughParametricSpecialize_bilinear, ih,
      finiteVectorPolynomialAdPower]

omit [Module ℚ E] in
theorem roughParametricSpecialize_sum (n : ℕ) (p : ℕ → RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize (roughParametricSum n p) x =
      finiteVectorPolynomialSum n (fun j => roughParametricSpecialize (p j) x) := by
  simp only [roughParametricSpecialize, roughParametricSum, finiteVectorPolynomialSum,
    List.map_flatten, List.map_map, Function.comp_def]

omit [Module ℚ E] in
theorem roughParametricEndpoint_eval (p : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughVectorMvEval (roughParametricEndpoint p) x =
      finiteVectorPolynomialEval (roughParametricSpecialize p x) 1 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change roughVectorMvEval (a.2 ++ roughParametricEndpoint p) x =
      1 ^ a.1 • roughVectorMvEval a.2 x + finiteVectorPolynomialEval (roughParametricSpecialize p x) 1
    rw [roughVectorMvEval_append, ih, one_pow, one_smul]

end Hindman168
