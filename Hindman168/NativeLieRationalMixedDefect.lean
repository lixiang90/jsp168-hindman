import Hindman168.FiniteVectorPolynomialMixedSubspaces
import Hindman168.NativeLieRationalFieldPolynomial

/-! Mixed rational layers of the actual native dexp defect. Positive
defect powers improve the layer of the second input. The zero power is
kept explicitly; no closure of a rational subspace is assumed. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalDefectPolynomial_coefficients_mem_mixed
    (V F N : Submodule ℚ E) (hNF : N ≤ F)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem F q) :
    finiteVectorPolynomialCoefficientsMem N
      (nativeLieRationalDefectPolynomial (I := I) (G := G) p q) := by
  apply finiteVectorPolynomialCoefficientsMem_sum
  intro n _
  apply finiteVectorPolynomialCoefficientsMem_scale
  exact finiteVectorPolynomialCoefficientsMem_adPower_positive_mixed V F N hNF _ hB hp hq n

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalDefectPowerPolynomial_positive_coefficients_mem_mixed
    (V F N : Submodule ℚ E) (hNF : N ≤ F)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem F q) (n : ℕ) :
    finiteVectorPolynomialCoefficientsMem N
      (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q (n + 1)) := by
  induction n with
  | zero => exact nativeLieRationalDefectPolynomial_coefficients_mem_mixed V F N hNF hB hp hq
  | succ n ih =>
    exact nativeLieRationalDefectPolynomial_coefficients_mem_mixed V F N hNF hB hp
      (finiteVectorPolynomialCoefficientsMem_mono hNF ih)

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalFieldPolynomial_split_zero
    (hc : 0 < Group.nilpotencyClass G) (p q : List (ℕ × E)) :
    nativeLieRationalFieldPolynomial (I := I) (G := G) p q =
      q ++ finiteVectorPolynomialSum (Group.nilpotencyClass G - 1)
        (fun j => nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q (j + 1)) := by
  unfold nativeLieRationalFieldPolynomial
  have he : Group.nilpotencyClass G = (Group.nilpotencyClass G - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.succ_le_of_lt hc)).symm
  calc
    _ = finiteVectorPolynomialSum ((Group.nilpotencyClass G - 1) + 1)
      (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q) :=
        congrArg (fun k => finiteVectorPolynomialSum k
          (nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q)) he
    _ = _ := finiteVectorPolynomialSum_zero_split _ _

omit [CompleteSpace E] [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G] in
 theorem nativeLieRationalFieldPolynomial_positive_tail_coefficients_mem
    (V F N : Submodule ℚ E) (hNF : N ≤ F)
    (hB : ∀ v ∈ V, ∀ w ∈ F, nativeLieAdjointDifferential (I := I) (G := G) v w ∈ N)
    {p q : List (ℕ × E)} (hp : finiteVectorPolynomialCoefficientsMem V p)
    (hq : finiteVectorPolynomialCoefficientsMem F q) :
    finiteVectorPolynomialCoefficientsMem N
      (finiteVectorPolynomialSum (Group.nilpotencyClass G - 1)
        (fun j => nativeLieRationalDefectPowerPolynomial (I := I) (G := G) p q (j + 1))) := by
  apply finiteVectorPolynomialCoefficientsMem_sum
  intro j _
  exact nativeLieRationalDefectPowerPolynomial_positive_coefficients_mem_mixed V F N hNF hB hp hq j

end Hindman168
