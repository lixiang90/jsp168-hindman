import Hindman168.RelativeSquareTerminalCenter
import Hindman168.SubgroupFiltrationTransport

/-! The actual filtration inside the relative-square group itself.
Both initial layers are the whole relative group; the terminal layer
is the actual internal diagonal of the original terminal layer. -/

namespace Hindman168
variable {G : Type*} [Group G]

def relativeSquareInternalFiltration (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (i : ℕ) :
    Subgroup (relativeSquareFiltration F hN 1) :=
  (relativeSquareFiltration F hN i).comap (relativeSquareFiltration F hN 1).subtype

theorem relative_square_internal_filtration_conditions (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) :
    CubeGroupFiltration (relativeSquareInternalFiltration F hN) :=
  (relative_square_filtration_conditions F hN hF).comap _

theorem relative_square_internal_filtration_zero (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) :
    relativeSquareInternalFiltration F hN 0 = ⊤ := by
  apply top_unique
  intro p _
  exact relative_square_filtration_antitone F hN hF (Nat.zero_le 1) p.property

theorem relative_square_internal_filtration_one (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) : relativeSquareInternalFiltration F hN 1 = ⊤ := by
  apply top_unique
  intro p _
  exact p.property

theorem relative_square_internal_terminal_diagonal (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (d : ℕ) (hd : F (d+1) = ⊥) :
    relativeSquareInternalFiltration F hN d =
      (relativeDiagonalSubgroup (F d)).comap (relativeSquareFiltration F hN 1).subtype := by
  unfold relativeSquareInternalFiltration
  rw [relative_square_filtration_terminal_diagonal F hN d hd]

theorem relative_square_internal_terminal_normal (F : ℕ → Subgroup G)
    (hN : ∀ i, (F i).Normal) (hF : CubeGroupFiltration F) (h1 : F 1 = ⊤)
    (d : ℕ) (hd : F (d+1) = ⊥) :
    (relativeSquareInternalFiltration F hN d).Normal := by
  rw [relative_square_internal_terminal_diagonal F hN d hd]
  letI := relative_terminal_diagonal_normal F hF h1 d hd
  infer_instance

end Hindman168
