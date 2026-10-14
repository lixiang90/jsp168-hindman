import Hindman168.AveragedInvariantFactorCauchy
import Hindman168.CubeCopyElimination
import Hindman168.RetainedRootCube

namespace Hindman168
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]

theorem averaged_rootResponse_factor_cauchy {d : ℕ}
    (D : Q →+ (G × (Fin d → Q))) [Fintype D.range]
    (hD : ∀ a, (D a).1 = (a : G))
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (f g : ι → α → (G × (Fin d → Q)) → ℝ) (C : ℝ)
    (hf : ∀ c u z, |f c u z| ≤ C)
    (hinv : ∀ c u z a, f c u (z + D a) = f c u z) :
    (∑ c, p c * finiteHaarMean (fun u => finiteHaarMean (fun z => f c u z * g c u z))) ^ 2 ≤
      C ^ 2 * ∑ c, p c * finiteHaarMean (fun u => finiteHaarMean
        (fun z => finiteHaarMean (fun a : Q => g c u z * g c u (z + D a)))) := by
  have hi (c : ι) (u : α) (z : G × (Fin d → Q)) (a : D.range) :
      f c u (z + a) = f c u z := by
    obtain ⟨b, hb⟩ := a.property
    rw [← hb]
    exact hinv c u z b
  have he (c : ι) (u : α) (z : G × (Fin d → Q)) :
      finiteHaarMean (fun a : D.range => g c u z * g c u (z + a)) =
        finiteHaarMean (fun a : Q => g c u z * g c u (z + D a)) :=
    (rootResponseDirection_haar Q D hD _).symm
  simpa only [he] using
    averaged_subgroup_invariant_factor_cauchy D.range p hp hsum f g C hf hi

theorem averaged_cubeVertexCopies_cauchy {d : ℕ}
    {ι α κ : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (s : Finset κ) (b : ι → α → κ → G × (Fin d → Q))
    (h : ι → G → ℝ) (hh : ∀ c x, |h c x| ≤ 1)
    (ω : Finset (Fin d)) (j : Fin d) [Fintype (cubeVertexFixingDirection Q d j).range]
    (hj : j ∈ ω) (g : ι → α → (G × (Fin d → Q)) → ℝ) :
    (∑ c, p c * finiteHaarMean (fun u => finiteHaarMean
      (fun z => (∏ t ∈ s, h c (cubeVertexEvaluation Q d ω (z + b c u t))) * g c u z))) ^ 2 ≤
      ∑ c, p c * finiteHaarMean (fun u => finiteHaarMean
        (fun z => finiteHaarMean (fun a : Q => g c u z *
          g c u (z + cubeVertexFixingDirection Q d j a)))) := by
  apply le_trans (averaged_rootResponse_factor_cauchy Q
    (cubeVertexFixingDirection Q d j) (fun _ => rfl) p hp hsum _ g 1
    (fun c u => cubeVertexCopies_abs_le_one Q d s (b c u) (h c) (hh c) ω)
    (fun c u z a => by
      simp only [cubeVertexEvaluation_translated_copy_fixed Q d ω j hj]))
  simp only [one_pow, one_mul, le_refl]

theorem averaged_cubeDensity_cauchy {d : ℕ}
    [Fintype (subgroupCubeRootDirection Q d).range]
    {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α]
    (p : ι → ℝ) (hp : ∀ c, 0 ≤ p c) (hsum : ∑ c, p c = 1)
    (ρ : ι → α → (Fin d → Q) → ℝ) (C : ℝ) (hρ : ∀ c u v, |ρ c u v| ≤ C)
    (g : ι → α → (G × (Fin d → Q)) → ℝ) :
    (∑ c, p c * finiteHaarMean (fun u => finiteHaarMean (fun z => ρ c u z.2 * g c u z))) ^ 2 ≤
      C ^ 2 * ∑ c, p c * finiteHaarMean (fun u => finiteHaarMean
        (fun z => finiteHaarMean (fun a : Q => g c u z *
          g c u (z + subgroupCubeRootDirection Q d a)))) := by
  exact averaged_rootResponse_factor_cauchy Q (subgroupCubeRootDirection Q d)
    (fun _ => rfl) p hp hsum _ g C (fun c u z => hρ c u z.2)
    (fun c u z a => congrArg (ρ c u) (subgroupCubeRootDirection_preserves_increments Q d z a))

end Hindman168
