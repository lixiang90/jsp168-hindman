import Hindman168.SubgroupCubeReflection

namespace Hindman168
open scoped BigOperators Classical symmDiff

noncomputable def subgroupMixedCubeAverage {G : Type*} [AddCommGroup G] [Fintype G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ) : ℝ :=
  finiteHaarMean (fun x => finiteHaarMean (fun v : Fin d → Q =>
    ∏ ω : Finset (Fin d), f ω (x + ∑ j ∈ ω, (v j : G))))

noncomputable def subgroupVertexDual {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) (x : G) : ℝ :=
  finiteHaarMean (fun v : Fin d → Q =>
    ∏ ω ∈ (Finset.univ : Finset (Finset (Fin d))).erase S,
      f ω (x + ∑ j ∈ S ∆ ω, (v j : G)))

theorem subgroupMixedCubeAverage_vertex_correlation {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (S : Finset (Fin d)) (f : Finset (Fin d) → G → ℝ) :
    subgroupMixedCubeAverage Q d f =
      finiteHaarMean (fun x => f S x * subgroupVertexDual Q d S f x) := by
  unfold subgroupMixedCubeAverage subgroupVertexDual
  rw [← subgroupCube_mixed_vertex_reflection Q d S f]
  simp only [← finiteHaarMean_const_mul]
  congr 1
  funext x
  congr 1
  funext v
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ S)]
  simp [symmDiff_self]

theorem subgroupVertexDual_abs_le_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f : Finset (Fin d) → G → ℝ) (hf : ∀ ω, ω ≠ S → ∀ x, |f ω x| ≤ 1) (x : G) :
    |subgroupVertexDual Q d S f x| ≤ 1 := by
  apply finiteHaarMean_abs_le_one
  intro v
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun ω hω => hf ω (Finset.mem_erase.mp hω).1 _)

theorem subgroupVertexDual_congr_off_vertex {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (S : Finset (Fin d))
    (f g : Finset (Fin d) → G → ℝ) (h : ∀ ω, ω ≠ S → f ω = g ω) :
    subgroupVertexDual Q d S f = subgroupVertexDual Q d S g := by
  funext x
  unfold subgroupVertexDual
  congr 1
  funext v
  exact Finset.prod_congr rfl (fun ω hω => congrFun (h ω (Finset.mem_erase.mp hω).1) _)

theorem subgroupMixedCubeAverage_replace_vertex {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (S : Finset (Fin d)) (f g : Finset (Fin d) → G → ℝ)
    (hf : ∀ ω, ω ≠ S → ∀ x, |f ω x| ≤ 1)
    (h : ∀ ω, ω ≠ S → f ω = g ω) :
    |subgroupMixedCubeAverage Q d f - subgroupMixedCubeAverage Q d g| ≤
      finiteHaarMean (fun x => |f S x - g S x|) := by
  rw [subgroupMixedCubeAverage_vertex_correlation Q d S f,
    subgroupMixedCubeAverage_vertex_correlation Q d S g,
    ← subgroupVertexDual_congr_off_vertex Q d S f g h, ← finiteHaarMean_sub]
  refine (finiteHaarMean_abs_mean_le _).trans (finiteHaarMean_mono _ _ ?_)
  intro x
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (subgroupVertexDual_abs_le_one Q d S f hf x)

theorem weighted_subgroupMixedCubeAverage_replace_vertex {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (S : Finset (Fin d)) (p : κ → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hs : ∑ c, p c = 1)
    (f g : κ → Finset (Fin d) → G → ℝ)
    (hf : ∀ c ω, ω ≠ S → ∀ x, |f c ω x| ≤ 1)
    (h : ∀ c ω, ω ≠ S → f c ω = g c ω) :
    ((∑ c, p c * subgroupMixedCubeAverage Q d (f c)) -
      ∑ c, p c * subgroupMixedCubeAverage Q d (g c)) ^ 2 ≤
      ∑ c, p c * finiteHaarMean (fun x => (f c S x - g c S x) ^ 2) := by
  have he : (∑ c, p c * subgroupMixedCubeAverage Q d (f c)) -
      ∑ c, p c * subgroupMixedCubeAverage Q d (g c) =
      ∑ c, p c * finiteHaarMean (fun x =>
        subgroupVertexDual Q d S (f c) x * (f c S x - g c S x)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← mul_sub, subgroupMixedCubeAverage_vertex_correlation Q d S (f c),
      subgroupMixedCubeAverage_vertex_correlation Q d S (g c),
      ← subgroupVertexDual_congr_off_vertex Q d S (f c) (g c) (h c),
      ← finiteHaarMean_sub]
    congr 1
    congr 1
    funext x
    ring
  rw [he]
  exact weightedHaar_discard_unit_factor p hp hs
    (fun c => subgroupVertexDual Q d S (f c)) (fun c x => f c S x - g c S x)
    (fun c x => subgroupVertexDual_abs_le_one Q d S (f c) (hf c) x)

end Hindman168
