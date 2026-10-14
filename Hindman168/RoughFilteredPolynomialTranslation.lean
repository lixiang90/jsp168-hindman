import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Defs

namespace Hindman168

def roughGroupDifference {V G : Type*} [AddCommMonoid V] [Group G]
    (P : V → G) (h x : V) : G := P (x+h)*(P x)⁻¹

def roughIteratedGroupDifference {V G : Type*} [AddCommMonoid V] [Group G]
    (P : V → G) : List V → V → G
  | [] => P
  | h :: hs => roughGroupDifference (roughIteratedGroupDifference P hs) h

def RoughFilteredPolynomial {V G : Type*} [AddCommMonoid V] [Group G]
    (F : ℕ → Subgroup G) (P : V → G) : Prop :=
  ∀ (hs : List V) (x : V), roughIteratedGroupDifference P hs x ∈ F hs.length

theorem rough_group_difference_translate {V G : Type*} [AddCommMonoid V] [Group G]
    (P : V → G) (a h x : V) :
    roughGroupDifference (fun y => P (y+a)) h x = roughGroupDifference P h (x+a) := by
  simp only [roughGroupDifference, add_right_comm]

theorem rough_iterated_group_difference_translate {V G : Type*} [AddCommMonoid V] [Group G]
    (P : V → G) (a : V) (hs : List V) :
    roughIteratedGroupDifference (fun y => P (y+a)) hs =
      fun x => roughIteratedGroupDifference P hs (x+a) := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext x
    simp only [roughIteratedGroupDifference, ih, rough_group_difference_translate]

theorem rough_filtered_polynomial_translate {V G : Type*} [AddCommMonoid V] [Group G]
    (F : ℕ → Subgroup G) (P : V → G) (hP : RoughFilteredPolynomial F P) (a : V) :
    RoughFilteredPolynomial F (fun y => P (y+a)) := by
  intro hs x
  rw [rough_iterated_group_difference_translate]
  exact hP hs (x+a)

theorem rough_group_difference_zero {V G : Type*} [AddCommMonoid V] [Group G]
    (P : V → G) (x : V) : roughGroupDifference P 0 x = 1 := by
  simp [roughGroupDifference]

end Hindman168
