import Hindman168.MixedDualProductClosure
import Mathlib.Analysis.Convex.Combination

namespace Hindman168
open scoped BigOperators Classical

/-- Finite convex combinations of actual unit-input mixed dual functions. -/
noncomputable def subgroupMixedDualHull {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) : Set (G → ℝ) :=
  convexHull ℝ {h | ∃ f : Finset (Fin d) → G → ℝ,
    (∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1) ∧ h = subgroupMixedDualFunction Q d f}

theorem convex_finiteHaarMean_mem {X A : Type*} [Fintype A] [Nonempty A]
    (S : Set (X → ℝ)) (hS : Convex ℝ S) (f : A → X → ℝ)
    (hf : ∀ a, f a ∈ S) : (fun x => finiteHaarMean (fun a => f a x)) ∈ S := by
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := hS.sum_mem (t := Finset.univ) (w := fun _ : A => (Fintype.card A : ℝ)⁻¹)
    (z := f) (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [hc]) (fun a _ => hf a)
  convert h using 1
  ext x
  simp [finiteHaarMean, Finset.sum_apply, div_eq_mul_inv, Finset.mul_sum, mul_comm]

theorem subgroupMixedDualFunction_mem_hull {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (f : Finset (Fin d) → G → ℝ)
    (hf : ∀ ω, ω ≠ ∅ → ∀ x, |f ω x| ≤ 1) :
    subgroupMixedDualFunction Q d f ∈ subgroupMixedDualHull Q d :=
  subset_convexHull ℝ _ ⟨f, hf, rfl⟩

theorem subgroupMixedDualFunction_product_mem_hull {G ι : Type*}
    [AddCommGroup G] [Fintype ι] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (f : ι → Finset (Fin d) → G → ℝ)
    (hf : ∀ i ω, ω ≠ ∅ → ∀ x, |f i ω x| ≤ 1) :
    (fun x => ∏ i, subgroupMixedDualFunction Q d (f i) x) ∈ subgroupMixedDualHull Q d := by
  simp_rw [subgroupMixedDualFunction_product_average Q d f]
  apply convex_finiteHaarMean_mem _ (convex_convexHull ℝ _)
  intro a
  apply subgroupMixedDualFunction_mem_hull
  intro ω hω x
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hf i ω hω _)

theorem subgroupMixedDualHull_mul_mem {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) {u v : G → ℝ}
    (hu : u ∈ subgroupMixedDualHull Q d) (hv : v ∈ subgroupMixedDualHull Q d) :
    u * v ∈ subgroupMixedDualHull Q d := by
  have hconv : Convex ℝ (subgroupMixedDualHull Q d) := convex_convexHull ℝ _
  have hright (a : G → ℝ) : Convex ℝ {b | a * b ∈ subgroupMixedDualHull Q d} := by
    intro x hx y hy r s hr hs hrs
    change a * (r • x + s • y) ∈ subgroupMixedDualHull Q d
    simpa only [subgroupMixedDualHull, mul_add, mul_smul_comm] using hconv hx hy hr hs hrs
  have hleft (b : G → ℝ) : Convex ℝ {a | a * b ∈ subgroupMixedDualHull Q d} := by
    intro x hx y hy r s hr hs hrs
    change (r • x + s • y) * b ∈ subgroupMixedDualHull Q d
    simpa only [subgroupMixedDualHull, add_mul, smul_mul_assoc] using hconv hx hy hr hs hrs
  apply convexHull_min (t := {a | a * v ∈ subgroupMixedDualHull Q d}) ?_ (hleft v) hu
  rintro a ⟨f, hf, rfl⟩
  apply convexHull_min (t := {b | subgroupMixedDualFunction Q d f * b ∈ subgroupMixedDualHull Q d})
    ?_ (hright _) hv
  rintro b ⟨g, hg, rfl⟩
  have h := subgroupMixedDualFunction_product_mem_hull Q d (fun i : Bool => if i then f else g)
    (by intro i; cases i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption)
  simpa [Fintype.prod_bool, mul_comm, Pi.mul_def] using h

theorem subgroupMixedDualHull_abs_le_one {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) {u : G → ℝ}
    (hu : u ∈ subgroupMixedDualHull Q d) (x : G) : |u x| ≤ 1 := by
  apply convexHull_min (t := {v : G → ℝ | |v x| ≤ 1}) ?_ ?_ hu
  · rintro v ⟨f, hf, rfl⟩
    exact subgroupMixedDualFunction_abs_le_one Q d f hf x
  · intro a ha b hb r s hr hs hrs
    change |r * a x + s * b x| ≤ 1
    calc
      _ ≤ |r * a x| + |s * b x| := abs_add_le _ _
      _ = r * |a x| + s * |b x| := by rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hs]
      _ ≤ r * 1 + s * 1 := add_le_add (mul_le_mul_of_nonneg_left ha hr) (mul_le_mul_of_nonneg_left hb hs)
      _ = 1 := by simpa using hrs

theorem subgroupMixedDualHull_correlation_le_gowers {G : Type*}
    [AddCommGroup G] [Fintype G] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) {u : G → ℝ} (hu : u ∈ subgroupMixedDualHull Q d)
    (g : G → ℝ) : |finiteHaarMean (fun x => g x * u x)| ≤ subgroupGowersValue Q d g := by
  apply convexHull_min (t := {v : G → ℝ |
    |finiteHaarMean (fun x => g x * v x)| ≤ subgroupGowersValue Q d g}) ?_ ?_ hu
  · rintro v ⟨f, hf, rfl⟩
    exact subgroupMixedDualFunction_correlation_le_gowers Q d hd f hf g
  · intro a ha b hb r s hr hs hrs
    change |finiteHaarMean (fun x => g x * (r * a x + s * b x))| ≤ _
    simp_rw [mul_add, mul_left_comm (g _) r, mul_left_comm (g _) s]
    rw [finiteHaarMean_add, finiteHaarMean_const_mul, finiteHaarMean_const_mul]
    calc
      _ ≤ |r * finiteHaarMean (fun x => g x * a x)| +
          |s * finiteHaarMean (fun x => g x * b x)| := abs_add_le _ _
      _ = r * |finiteHaarMean (fun x => g x * a x)| +
          s * |finiteHaarMean (fun x => g x * b x)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg hs]
      _ ≤ r * subgroupGowersValue Q d g + s * subgroupGowersValue Q d g :=
        add_le_add (mul_le_mul_of_nonneg_left ha hr) (mul_le_mul_of_nonneg_left hb hs)
      _ = subgroupGowersValue Q d g := by rw [← add_mul, hrs, one_mul]

theorem subgroupMixedDualHull_one_mem {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) :
    (1 : G → ℝ) ∈ subgroupMixedDualHull Q d := by
  have h := subgroupMixedDualFunction_mem_hull Q d (fun _ _ => 1) (by simp)
  have he : subgroupMixedDualFunction Q d (fun _ _ => 1) = (1 : G → ℝ) := by
    funext x
    simp [subgroupMixedDualFunction, finiteHaarMean_const]
  rwa [he] at h

theorem subgroupMixedDualHull_prod_mem {G ι : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) (s : Finset ι) (f : ι → G → ℝ)
    (hf : ∀ i ∈ s, f i ∈ subgroupMixedDualHull Q d) :
    (∏ i ∈ s, f i) ∈ subgroupMixedDualHull Q d := by
  induction s using Finset.induction_on with
  | empty => simpa using subgroupMixedDualHull_one_mem Q d
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact subgroupMixedDualHull_mul_mem Q d (hf a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem subgroupMixedDualHull_translate_mem {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ) {u : G → ℝ}
    (hu : u ∈ subgroupMixedDualHull Q d) (a : G) :
    (fun x => u (x + a)) ∈ subgroupMixedDualHull Q d := by
  apply convexHull_min (t := {v : G → ℝ |
    (fun x => v (x + a)) ∈ subgroupMixedDualHull Q d}) ?_ ?_ hu
  · rintro v ⟨f, hf, rfl⟩
    have h := subgroupMixedDualFunction_mem_hull Q d (fun ω y => f ω (y + a))
      (fun ω hω y => hf ω hω (y + a))
    change (fun x => subgroupMixedDualFunction Q d f (x + a)) ∈ subgroupMixedDualHull Q d
    convert h using 1
    funext x
    exact (subgroupMixedDualFunction_translate Q d f a x).symm
  · intro v hv w hw r s hr hs hrs
    exact (convex_convexHull ℝ _) hv hw hr hs hrs

theorem weighted_mixedDualHull_correlation_le_gowers {G κ : Type*}
    [AddCommGroup G] [Fintype G] [Fintype κ] (Q : AddSubgroup G) [Fintype Q]
    (d : ℕ) (hd : 0 < d) (p : κ → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hs : ∑ c, p c = 1) (u : κ → G → ℝ)
    (hu : ∀ c, u c ∈ subgroupMixedDualHull Q d) (g : κ → G → ℝ) :
    |∑ c, p c * finiteHaarMean (fun x => g c x * u c x)| ≤
      weightedSubgroupGowersValue Q p d g := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (probabilityWeighted_gowers_le_weightedGowers Q d hd p hp hs g)
  apply Finset.sum_le_sum
  intro c _
  rw [abs_mul, abs_of_nonneg (hp c)]
  exact mul_le_mul_of_nonneg_left
    (subgroupMixedDualHull_correlation_le_gowers Q d hd (hu c) (g c)) (hp c)

end Hindman168

