import Hindman168.RelativeSquareInternalFiltration

/-! Quotienting the ACTUAL internal terminal diagonal gives the ACTUAL
relative-square filtration with terminal index d, rather than d+1.
This is a filtration-degree statement, not a nilpotency-step claim. -/

namespace Hindman168
variable {G : Type*} [Group G]

def relativeSquareReducedFiltration (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) (i : ℕ) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    Subgroup ((relativeSquareFiltration F hN 1) ⧸ relativeSquareInternalFiltration F hN d) :=
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  (relativeSquareInternalFiltration F hN i).map
    (QuotientGroup.mk' (relativeSquareInternalFiltration F hN d))

theorem relative_square_reduced_filtration_conditions (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    CubeGroupFiltration (relativeSquareReducedFiltration F hN hF h1 d hd) := by
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  exact (relative_square_internal_filtration_conditions F hN hF).map _

theorem relative_square_reduced_filtration_zero (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    relativeSquareReducedFiltration F hN hF h1 d hd 0 = ⊤ := by
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  unfold relativeSquareReducedFiltration
  rw [relative_square_internal_filtration_zero F hN hF]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem relative_square_reduced_filtration_one (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    relativeSquareReducedFiltration F hN hF h1 d hd 1 = ⊤ := by
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  unfold relativeSquareReducedFiltration
  rw [relative_square_internal_filtration_one F hN]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem relative_square_reduced_filtration_terminal (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    relativeSquareReducedFiltration F hN hF h1 d hd d = ⊥ := by
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  exact subgroup_filtration_quotient_terminal _ _ d le_rfl

theorem relative_square_reduced_filtration_beyond_terminal (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) (i : ℕ) (hi : d ≤ i) :
    letI := relative_square_internal_terminal_normal F hN hF h1 d hd
    relativeSquareReducedFiltration F hN hF h1 d hd i = ⊥ := by
  letI := relative_square_internal_terminal_normal F hN hF h1 d hd
  apply le_antisymm _ bot_le
  rw [← relative_square_reduced_filtration_terminal F hN hF h1 d hd]
  exact (relative_square_reduced_filtration_conditions F hN hF h1 d hd).antitone hi

end Hindman168
