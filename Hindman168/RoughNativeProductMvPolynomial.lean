import Hindman168.RoughParametricPicard

namespace Hindman168
open scoped Manifold ContDiff

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

theorem roughNativeParametricDefect_specialize
    (p q : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize
      (roughParametricDefect (nativeLieAdjointDifferential (I := I) (G := G))
        (Group.nilpotencyClass G) p q) x =
      nativeLieRationalDefectPolynomial (I := I) (G := G)
        (roughParametricSpecialize p x) (roughParametricSpecialize q x) := by
  simp only [roughParametricDefect, nativeLieRationalDefectPolynomial,
    roughParametricSpecialize_sum, roughParametricSpecialize_scale, roughParametricSpecialize_ad]

theorem roughNativeParametricDefectPower_specialize
    (p q : RoughParametricCurve σ E) (n : ℕ) (x : σ → ℝ) :
    roughParametricSpecialize
      (roughParametricDefectPower (nativeLieAdjointDifferential (I := I) (G := G))
        (Group.nilpotencyClass G) p q n) x =
      nativeLieRationalDefectPowerPolynomial (I := I) (G := G)
        (roughParametricSpecialize p x) (roughParametricSpecialize q x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [roughParametricDefectPower, roughNativeParametricDefect_specialize,
      ih, nativeLieRationalDefectPowerPolynomial]

theorem roughNativeParametricField_specialize
    (p q : RoughParametricCurve σ E) (x : σ → ℝ) :
    roughParametricSpecialize
      (roughParametricField (nativeLieAdjointDifferential (I := I) (G := G))
        (Group.nilpotencyClass G) p q) x =
      nativeLieRationalFieldPolynomial (I := I) (G := G)
        (roughParametricSpecialize p x) (roughParametricSpecialize q x) := by
  simp only [roughParametricField, nativeLieRationalFieldPolynomial,
    roughParametricSpecialize_sum, roughNativeParametricDefectPower_specialize]

theorem roughNativeParametricPicard_specialize
    (w u : RoughVectorMvPolynomial σ E) (n : ℕ) (x : σ → ℝ) :
    roughParametricSpecialize
      (roughParametricPicard (nativeLieAdjointDifferential (I := I) (G := G))
        (Group.nilpotencyClass G) w u n) x =
      nativeLieRationalPicardPolynomial (I := I) (G := G)
        (roughVectorMvEval (E := E) w x) (roughVectorMvEval (E := E) u x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change roughParametricSpecialize ([(0,u)] ++ _) x = _
    simp only [roughParametricSpecialize, List.map_append, List.map_cons, List.map_nil]
    change [(0, roughVectorMvEval (E := E) u x)] ++ roughParametricSpecialize
      (roughParametricPrimitive (roughParametricField _ _
        (roughParametricPicard _ _ w u n) [(0,w)])) x = _
    rw [roughParametricSpecialize_primitive, roughNativeParametricField_specialize, ih]
    rfl

noncomputable def roughNativeProductMvPolynomial
    (u w : RoughVectorMvPolynomial σ E) : RoughVectorMvPolynomial σ E :=
  roughParametricEndpoint (roughParametricPicard
    (nativeLieAdjointDifferential (I := I) (G := G)) (Group.nilpotencyClass G)
    w u (Group.nilpotencyClass G + 1))

omit [Module ℚ E] in
theorem roughNativeProductMvPolynomial_degree
    {u w : RoughVectorMvPolynomial σ E} {d : ℕ}
    (hu : RoughVectorMvDegreeLE u d) (hw : RoughVectorMvDegreeLE w d) :
    RoughVectorMvDegreeLE (roughNativeProductMvPolynomial (I := I) (G := G) u w)
      (((Group.nilpotencyClass G * Group.nilpotencyClass G + 1) ^
        (Group.nilpotencyClass G + 1)) * d) :=
  roughParametricDegreeLE_endpoint (roughParametricPicard_degree _ _ hw hu _)

variable [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]
  [Group.IsNilpotent G] [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem roughNativeProductMvPolynomial_eval
    (u w : RoughVectorMvPolynomial σ E) (x : σ → ℝ) :
    roughVectorMvEval (E := E) (roughNativeProductMvPolynomial (I := I) (G := G) u w) x =
      nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) u x) *
          nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) w x)) := by
  rw [roughNativeProductMvPolynomial, roughParametricEndpoint_eval,
    roughNativeParametricPicard_specialize]
  exact nativeLieRationalProductPolynomial_endpoint (I := I) (G := G) _ _

end Hindman168
