import Hindman168.LocalKernelCounts
import Mathlib.Data.ZMod.QuotientRing

/-!
# Exact uniform CRT vector law

The actual CRT equivalence is applied to every base coordinate and then
transposed. Its pushforward is the independent product of the uniform
local vector laws. Local events consequently multiply exactly.
-/

namespace Hindman168.FiniteMass

open scoped BigOperators Classical

theorem uniformFintypeMass_pi {ι : Type*} [Fintype ι] [hι : DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] :
    uniformFintypeMass (∀ i, α i) = piMass (fun i => uniformFintypeMass (α i)) := by
  classical
  letI : DecidableEq ι := hι
  ext x
  rw [uniformFintypeMass_apply, piMass_apply, Fintype.card_pi, Nat.cast_prod,
    ← Finset.prod_inv_distrib]
  simp only [uniformFintypeMass_apply]

theorem event_piMass_forall {ι : Type*} [Fintype ι] [hι : DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, Mass (α i)) (E : ∀ i, α i → Prop) :
    event (piMass μ) (fun x => ∀ i, E i (x i)) = ∏ i, event (μ i) (E i) := by
  classical
  letI : DecidableEq ι := hι
  rw [event_eq_sum _ _ (Finset.subset_univ _)]
  have hterm (x : ∀ i, α i) :
      (@ite ℝ (∀ i, E i (x i)) (Classical.propDecidable _) (piMass μ x) 0) =
        ∏ i, if E i (x i) then μ i (x i) else 0 := by
    by_cases hx : ∀ i, E i (x i)
    · simp only [if_pos hx, piMass_apply, if_pos (hx _)]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_forall.mp hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hsum : (∑ x : (∀ i, α i), @ite ℝ (∀ i, E i (x i))
      (Classical.propDecidable _) (piMass μ x) 0) =
      ∑ x : (∀ i, α i), ∏ i, if E i (x i) then μ i (x i) else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    exact hterm x
  change (∑ x : (∀ i, α i), @ite ℝ (∀ i, E i (x i))
    (Classical.propDecidable _) (piMass μ x) 0) = _
  rw [hsum]
  have hright : (∏ i, event (μ i) (E i)) =
      ∏ i, ∑ a : α i, if E i a then μ i a else 0 := by
    apply Finset.prod_congr rfl
    intro i _
    simpa only [Finset.mem_univ, if_true] using event_eq_sum (μ i) (E i) (Finset.subset_univ _)
  rw [hright, Finset.prod_univ_sum, Fintype.piFinset_univ]

end Hindman168.FiniteMass

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def crtVectorAddEquiv {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hc : Pairwise (fun i j => (m i).Coprime (m j))) (d : ℕ) :
    (Fin d → ZMod (∏ i, m i)) ≃+ (∀ i, Fin d → ZMod (m i)) := by
  classical
  let e := ZMod.prodEquivPi m hc
  exact
    { toFun := fun x i j => e (x j) i
      invFun := fun y j => e.symm (fun i => y i j)
      left_inv := fun x => by funext j; exact e.left_inv (x j)
      right_inv := fun y => by
        funext i j
        exact congrFun (e.right_inv (fun i => y i j)) i
      map_add' := fun x y => by
        funext i j
        exact congrFun (map_add e (x j) (y j)) i }

theorem crtVectorAddEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (d : ℕ) (x : Fin d → ZMod (∏ i, m i)) (i : ι) (j : Fin d) :
    crtVectorAddEquiv m hc d x i j =
      ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i)) (x j) :=
  ZMod.prodEquivPi_apply m hc (x j) i

theorem uniformFintypeMass_crt_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j))) (d : ℕ) :
    (uniformFintypeMass (Fin d → ZMod (∏ i, m i))).mapDomain (crtVectorAddEquiv m hc d) =
      piMass (fun i => uniformFintypeMass (Fin d → ZMod (m i))) := by
  change (uniformFintypeMass (Fin d → ZMod (∏ i, m i))).mapDomain
    (crtVectorAddEquiv m hc d).toAddMonoidHom = _
  rw [uniformFintypeMass_addGroup_push (crtVectorAddEquiv m hc d).toAddMonoidHom
    (crtVectorAddEquiv m hc d).surjective]
  exact uniformFintypeMass_pi

theorem crtVector_event_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j))) (d : ℕ)
    (E : ∀ i, (Fin d → ZMod (m i)) → Prop) :
    event (uniformFintypeMass (Fin d → ZMod (∏ i, m i)))
      (fun x => ∀ i, E i (crtVectorAddEquiv m hc d x i)) =
      ∏ i, event (uniformFintypeMass (Fin d → ZMod (m i))) (E i) := by
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod (∏ i, m i)))
    (crtVectorAddEquiv m hc d) (fun y => ∀ i, E i (y i))
  rw [uniformFintypeMass_crt_vector, event_piMass_forall] at hmap
  exact hmap.symm

end Hindman168
