import Hindman168.UnitriangularRationalSupportInduction
import Mathlib.Topology.Algebra.Monoid

/-! Compact representatives for every actual rational strict matrix Lie
subgroup relative to the original integer group lattice. Strong induction
on real dimension chooses a shallowest nonzero support layer and an actual
lattice pivot, cuts to a strictly smaller rational slice, and multiplies its
constructed compact representatives by the pivot's compact unit segment.
No abelian restriction, supplied compact quotient, normal lattice or additive
closure of nonabelian lattice logarithms is used. -/

noncomputable section
namespace Hindman168
open Matrix Set Module
open scoped Pointwise

variable {n : ℕ}
local instance compactRepresentativesMatrixLieRing : LieRing (Matrix (Fin n) (Fin n) ℝ) :=
  LieRing.ofAssociativeRing

 def UnitriangularLieCompactRepresentatives
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) : Prop :=
  ∃ K : Set (Unitriangular n ℝ), IsCompact K ∧
    K ⊆ (unitriangularLieSubgroup V hV : Set (Unitriangular n ℝ)) ∧
    ∀ g ∈ unitriangularLieSubgroup V hV,
      ∃ x ∈ K, ∃ γ ∈ integerUnitriangularLattice n, g = x * γ

 theorem unitriangularLieCompactRepresentatives_zero
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ) (h0 : V.toSubmodule = ⊥) :
    UnitriangularLieCompactRepresentatives V hV := by
  refine ⟨{1}, isCompact_singleton, ?_, ?_⟩
  · intro g hg
    rw [mem_singleton_iff] at hg
    subst g
    exact (unitriangularLieSubgroup V hV).one_mem
  · intro g hg
    have hlog : (unitriangularLogarithm g).val = 0 := by
      change (unitriangularLogarithm g).val ∈ V.toSubmodule at hg
      rw [h0] at hg
      exact hg
    have hlog' : unitriangularLogarithm g = 0 := Subtype.ext hlog
    have hg1 : g = 1 := by
      rw [← unitriangularExponential_logarithm g, hlog']
      apply unitriangular_val_injective
      exact matrixFiniteExp_zero
    exact ⟨1, mem_singleton 1, 1, (integerUnitriangularLattice n).one_mem, by simp [hg1]⟩

 theorem unitriangularLieCompactRepresentatives_pivot_lift
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (k : ℕ) (hk : 1 ≤ k) (hdepth : V ≤ matrixDepthLieSubalgebra n k ℝ)
    (a b : Fin n) (hab : b.val < a.val + k + 1) (γ : Unitriangular n ℝ)
    (hγ : γ ∈ unitriangularLieSubgroup V hV) (hγZ : γ ∈ integerUnitriangularLattice n)
    (hneq : (unitriangularLogarithm γ).val a b ≠ 0)
    (hnext : UnitriangularLieCompactRepresentatives
      (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun i j => i = a ∧ j = b)
        (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hab)) (inf_le_left.trans hV)) :
    UnitriangularLieCompactRepresentatives V hV := by
  let W := V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun i j => i = a ∧ j = b)
    (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hab)
  obtain ⟨K, hK, hsub, hrep⟩ := hnext
  let A : Set (Unitriangular n ℝ) :=
    (fun r : ℝ => unitriangularExponential (r • unitriangularLogarithm γ)) '' Icc 0 1
  have hA : IsCompact A := unitriangularOneParameter_segment_isCompact _
  refine ⟨A * K, hA.mul hK, ?_, ?_⟩
  · rintro g ⟨c, hc, x, hx, rfl⟩
    obtain ⟨r, _, rfl⟩ := hc
    have he : unitriangularExponential (r • unitriangularLogarithm γ) ∈
        unitriangularLieSubgroup V hV := by
      change (unitriangularLogarithm (unitriangularExponential (r • unitriangularLogarithm γ))).val ∈ V
      rw [unitriangularLogarithm_exponential]
      exact V.smul_mem r hγ
    exact (unitriangularLieSubgroup V hV).mul_mem he (hsub hx).1
  · intro g hg
    have hγold : γ ∈ unitriangularLieSubgroup
        (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun _ _ => False)
          (by intro i j h; exact False.elim h)) (inf_le_left.trans hV) :=
      ⟨hγ, hdepth hγ, fun _ _ h => False.elim h⟩
    have hgold : g ∈ unitriangularLieSubgroup
        (V ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun _ _ => False)
          (by intro i j h; exact False.elim h)) (inf_le_left.trans hV) :=
      ⟨hg, hdepth hg, fun _ _ h => False.elim h⟩
    obtain ⟨r, hr, u, hu, z, hz, heq⟩ :=
      unitriangularSupportSlice_lattice_reduction_step V hV k hk (fun _ _ => False)
        (by intro i j h; exact False.elim h) a b hab γ hγold hγZ hneq g hgold
    have huW : u ∈ unitriangularLieSubgroup W (inf_le_left.trans hV) :=
      ⟨hu.1, hu.2.1, fun i j hij => hu.2.2 i j (Or.inr hij)⟩
    obtain ⟨x, hx, η, hη, huEq⟩ := hrep u huW
    refine ⟨unitriangularExponential (r • unitriangularLogarithm γ) * x,
      ⟨unitriangularExponential (r • unitriangularLogarithm γ), ⟨r, hr, rfl⟩, x, hx, rfl⟩,
      η * γ ^ z, (integerUnitriangularLattice n).mul_mem hη hz, ?_⟩
    rw [heq, huEq]
    simp only [mul_assoc]

 theorem rationalUnitriangularLieSubalgebra_compact_representatives
    (V : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hV : V ≤ strictUpperTriangularLieSubalgebra n ℝ)
    (hRat : RationalUnitriangularLieSubalgebra V) :
    UnitriangularLieCompactRepresentatives V hV := by
  have hmain : ∀ d : ℕ, ∀ W : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℝ),
      ∀ hW : W ≤ strictUpperTriangularLieSubalgebra n ℝ,
      RationalUnitriangularLieSubalgebra W → finrank ℝ W.toSubmodule = d →
        UnitriangularLieCompactRepresentatives W hW := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro W hW hRatW hdim
      by_cases h0 : W.toSubmodule = ⊥
      · exact unitriangularLieCompactRepresentatives_zero W hW h0
      · obtain ⟨k, hk, hdepth, X, hX, a, b, hab, hneq⟩ :=
          unitriangularLieSubalgebra_first_support W hW h0
        have hbound : b.val < a.val + k + 1 := by omega
        obtain ⟨γ, hγ, hγZ, hγneq⟩ :=
          rationalUnitriangularLieSubalgebra_original_lattice_pivot W hW hRatW a b hX hneq
        let U := W ⊓ matrixSupportSliceLieSubalgebra n k ℝ hk (fun i j => i = a ∧ j = b)
          (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hbound)
        have hU : U ≤ strictUpperTriangularLieSubalgebra n ℝ := inf_le_left.trans hW
        have hRatU : RationalUnitriangularLieSubalgebra U :=
          rationalUnitriangularLieSubalgebra_inf_supportSlice W hW hRatW k hk
            (fun i j => i = a ∧ j = b)
            (by intro i j h; rcases h with ⟨rfl, rfl⟩; exact hbound)
        have hlt : finrank ℝ U.toSubmodule < d := by
          rw [← hdim]
          exact unitriangularLieSubalgebra_pivot_slice_finrank_lt W k hk a b hbound hX hneq
        exact unitriangularLieCompactRepresentatives_pivot_lift W hW k hk hdepth a b hbound
          γ hγ hγZ hγneq (ih _ hlt U hU hRatU rfl)
  exact hmain _ V hV hRat rfl

end Hindman168
