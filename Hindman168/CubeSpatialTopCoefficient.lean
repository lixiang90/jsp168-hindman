import Hindman168.CubeBinomialCoefficient
import Hindman168.RoughAffineCommonMultiplier
import Mathlib.Logic.Equiv.Fin.Basic

/-! Every cube variable is spatial. Translation and fixed uniform dilation
transport the isolated TOP coefficient exactly. -/
namespace Hindman168
open MvPolynomial
open scoped BigOperators

def cubeSpatialVariableEquiv (d : ℕ) : Option (Fin d) ≃ Fin (d+1) :=
  (finSuccEquiv' (0 : Fin (d+1))).symm

theorem cube_spatial_variable_none (d : ℕ) : cubeSpatialVariableEquiv d none = 0 := rfl

theorem cube_spatial_variable_some {d : ℕ} (i : Fin d) :
    cubeSpatialVariableEquiv d (some i) = i.succ := by
  simp [cubeSpatialVariableEquiv]

noncomputable def cubeSpatialMonomial {d : ℕ} (j : ℕ) (A : Finset (Fin d)) : Fin (d+1) →₀ ℕ :=
  (cubeIsolatedMonomial j A).mapDomain (cubeSpatialVariableEquiv d)

theorem cube_spatial_monomial_degree {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (hA : A.card ≤ j) : (cubeSpatialMonomial j A).sum (fun _ n => n) = j := by
  rw [cubeSpatialMonomial, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact cube_isolated_monomial_degree j A hA

theorem cube_spatial_monomial_weight {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (hA : A.card ≤ j) : ∑ i, cubeSpatialMonomial j A i = j := by
  have he := cube_spatial_monomial_degree j A hA
  rw [Finsupp.sum_fintype _ _ (by simp)] at he
  exact he

theorem cube_spatial_top_coefficient {d : ℕ} (j : ℕ) (A : Finset (Fin d))
    (hA : A.card ≤ j) (p : MvPolynomial (Option (Fin d)) ℝ) (hp : p.totalDegree ≤ j)
    (b : Fin (d+1) → ℝ) (t : ℝ) :
    coeff (cubeSpatialMonomial j A)
      (roughMvAffineSubstitution b (fun _ => t) (rename (cubeSpatialVariableEquiv d) p)) =
      t^j * coeff (cubeIsolatedMonomial j A) p := by
  have he : Finsupp.equivFunOnFinite.symm (fun i => cubeSpatialMonomial j A i) =
      cubeSpatialMonomial j A := by ext i; simp
  have hd : (rename (cubeSpatialVariableEquiv d) p).totalDegree ≤
      (cubeSpatialMonomial j A).sum (fun _ n => n) := by
    rw [cube_spatial_monomial_degree j A hA]
    exact (totalDegree_rename_le _ _).trans hp
  conv_lhs => rw [← he]
  rw [rough_affine_uniform_coefficient, he, rough_translation_top_coefficient b _ _ hd,
    cube_spatial_monomial_weight j A hA]
  rw [cubeSpatialMonomial, coeff_rename_mapDomain _ (cubeSpatialVariableEquiv d).injective]

end Hindman168
