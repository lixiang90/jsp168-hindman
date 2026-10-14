import Hindman168.RoughFilteredPolynomialTranslation

namespace Hindman168

theorem rough_iterated_group_difference_precompose {V W G : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Group G] (P : W → G) (c : V →+ W)
    (hs : List V) (x : V) :
    roughIteratedGroupDifference (fun y => P (c y)) hs x =
      roughIteratedGroupDifference P (hs.map c) (c x) := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [roughIteratedGroupDifference, roughGroupDifference, List.map_cons, ih, map_add]

theorem rough_filtered_polynomial_precompose {V W G : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Group G] (F : ℕ → Subgroup G)
    (P : W → G) (hP : RoughFilteredPolynomial F P) (c : V →+ W) :
    RoughFilteredPolynomial F (fun x => P (c x)) := by
  intro hs x
  rw [rough_iterated_group_difference_precompose]
  simpa only [List.length_map] using hP (hs.map c) (c x)

end Hindman168
