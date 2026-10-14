import Hindman168.FiniteCentralQuotientCommutator
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! An actual finite set of finite-order generators gives a finite
abelianization. If the actual commutator subgroup is finite, the
original group is then finite by its genuine quotient map. -/

namespace Hindman168
open Set Subgroup

variable {G : Type*} [Group G]

theorem finite_abelianization_of_torsion_generators (s : Set G)
    (hsf : s.Finite) (hs : Subgroup.closure s = ⊤)
    (ht : ∀ g ∈ s, IsOfFinOrder g) : Finite (Abelianization G) := by
  letI : Group.FG G := Group.fg_iff.mpr ⟨s, hs, hsf⟩
  have hsur : Function.Surjective (Abelianization.of : G →* Abelianization G) :=
    QuotientGroup.mk_surjective
  letI : Group.FG (Abelianization G) := Group.fg_of_surjective hsur
  have hle : Subgroup.closure s ≤ (CommGroup.torsion (Abelianization G)).comap
      (Abelianization.of : G →* Abelianization G) := by
    apply (Subgroup.closure_le (K := (CommGroup.torsion (Abelianization G)).comap
      (Abelianization.of : G →* Abelianization G))).mpr
    intro g hg
    exact (Abelianization.of : G →* Abelianization G).isOfFinOrder (ht g hg)
  have htor : Monoid.IsTorsion (Abelianization G) := by
    intro x
    obtain ⟨g, rfl⟩ := hsur x
    exact hle (hs.symm ▸ Subgroup.mem_top g)
  exact CommGroup.finite_of_fg_torsion (Abelianization G) htor

theorem finite_of_finite_commutator_torsion_generators
    [Finite (_root_.commutator G)] (s : Set G)
    (hsf : s.Finite) (hs : Subgroup.closure s = ⊤)
    (ht : ∀ g ∈ s, IsOfFinOrder g) : Finite G := by
  letI : Finite (Abelianization G) :=
    finite_abelianization_of_torsion_generators s hsf hs ht
  apply (Abelianization.of.finite_iff_finite_ker_range (G := G)).mpr
  constructor
  · rw [Abelianization.ker_of]
    infer_instance
  · infer_instance

end Hindman168
