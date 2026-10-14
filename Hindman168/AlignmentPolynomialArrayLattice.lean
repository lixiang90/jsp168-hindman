import Hindman168.AlignmentArrayInputTranslations
import Mathlib.Topology.Algebra.Group.Quotient

/-! The genuine pointwise lattice condition and its nonnormal coset
space. No discreteness or cocompactness conclusion is assumed here. -/

namespace Hindman168

def alignmentPolynomialArrayLattice {σ G : Type*} [Group G] (Γ : Subgroup G) :
    Subgroup (alignmentPolynomialArrayGroup σ G) :=
  (Subgroup.pi Set.univ (fun _ : σ → ℤ => Γ)).comap (alignmentPolynomialArrayGroup σ G).subtype

theorem alignmentPolynomialArrayLattice_mem {σ G : Type*} [Group G]
    (Γ : Subgroup G) (f : alignmentPolynomialArrayGroup σ G) :
    f ∈ alignmentPolynomialArrayLattice Γ ↔ ∀ u : σ → ℤ, f.val u ∈ Γ := by
  simp only [alignmentPolynomialArrayLattice, Subgroup.mem_comap, Subgroup.mem_pi,
    Set.mem_univ, forall_const]
  rfl

theorem alignmentPolynomialArrayTranslation_lattice {σ G : Type*} [Group G]
    (Γ : Subgroup G) (v : σ → ℤ) (f : alignmentPolynomialArrayGroup σ G) :
    alignmentPolynomialArrayTranslation v f ∈ alignmentPolynomialArrayLattice Γ ↔
      f ∈ alignmentPolynomialArrayLattice Γ := by
  rw [alignmentPolynomialArrayLattice_mem, alignmentPolynomialArrayLattice_mem]
  constructor
  · intro h u
    have hu := h (u - v)
    change f.val ((u - v) + v) ∈ Γ at hu
    rw [sub_add_cancel] at hu
    exact hu
  · intro h u
    exact h (u + v)

noncomputable def alignmentPolynomialArrayCosetEvaluation {σ G : Type*} [Group G]
    (Γ : Subgroup G) (u : σ → ℤ) :
    alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ → G ⧸ Γ :=
  Quotient.lift (fun f : alignmentPolynomialArrayGroup σ G => (f.val u : G ⧸ Γ))
    (fun f h hfh => by
      apply QuotientGroup.eq.mpr
      have hmem := QuotientGroup.leftRel_apply.mp hfh
      exact (alignmentPolynomialArrayLattice_mem Γ (f⁻¹ * h)).mp hmem u)

theorem alignmentPolynomialArrayCosetEvaluation_mk {σ G : Type*} [Group G]
    (Γ : Subgroup G) (u : σ → ℤ) (f : alignmentPolynomialArrayGroup σ G) :
    alignmentPolynomialArrayCosetEvaluation Γ u
      (f : alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ) =
        (f.val u : G ⧸ Γ) := rfl

noncomputable def alignmentPolynomialArrayCosetTranslation {σ G : Type*} [Group G]
    (Γ : Subgroup G) (v : σ → ℤ) :
    alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ →
      alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ :=
  Quotient.lift (fun f : alignmentPolynomialArrayGroup σ G =>
      (alignmentPolynomialArrayTranslation v f :
        alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ))
    (fun f h hfh => by
      apply QuotientGroup.eq.mpr
      have hmem := QuotientGroup.leftRel_apply.mp hfh
      have hshift := (alignmentPolynomialArrayTranslation_lattice Γ v (f⁻¹ * h)).mpr hmem
      simpa only [map_mul, map_inv] using hshift)

theorem alignmentPolynomialArrayCosetTranslation_evaluation {σ G : Type*} [Group G]
    (Γ : Subgroup G) (v u : σ → ℤ)
    (y : alignmentPolynomialArrayGroup σ G ⧸ alignmentPolynomialArrayLattice Γ) :
    alignmentPolynomialArrayCosetEvaluation Γ u (alignmentPolynomialArrayCosetTranslation Γ v y) =
      alignmentPolynomialArrayCosetEvaluation Γ (u + v) y := by
  induction y using Quotient.inductionOn with
  | _ f => rfl

theorem alignmentPolynomialArrayCosetEvaluation_continuous {σ G : Type*} [Group G]
    [TopologicalSpace G] (Γ : Subgroup G) (u : σ → ℤ) :
    Continuous (alignmentPolynomialArrayCosetEvaluation Γ u) := by
  exact continuous_quot_lift _
    (QuotientGroup.continuous_mk.comp ((continuous_apply u).comp continuous_subtype_val))

end Hindman168
