import Hindman168.NilCornerReconstruction
import Hindman168.NilCornerLatticeRecovery

/-! Connect the proved lattice-recovery argument to the compact-corner
reconstruction and finite recipes. The certificate is an explicit proper
upper-face factorization for each element of a cube subgroup. Deriving
that certificate and compactness for the actual rational nilpotent Lie
cube group is still required, and is not replaced by a new axiom. -/

namespace Hindman168
open scoped Classical
open NNReal

variable {G : Type*} [Group G]

abbrev ProperCubeVertex (d : ℕ) := {E : Finset (Fin d) // E ≠ Finset.univ}

def ProperUpperFaceCoordinates {d : ℕ} (z : Finset (Fin d) → G) : Prop :=
  ∃ a : Finset (Fin d) → G, ∃ faces : List (Finset (Fin d)),
    (∀ D ∈ faces, D ≠ Finset.univ) ∧
    faces.Pairwise (fun D E => D.card ≤ E.card ∧ D ≠ E) ∧
    ∀ E, z E = upperFaceValue a faces E

noncomputable def cosetCornerCube {d : ℕ} (Γ : Subgroup G)
    (a : Finset (Fin d) → G) : Option (ProperCubeVertex d) → G ⧸ Γ :=
  fun j => match j with
    | none => (a Finset.univ : G ⧸ Γ)
    | some E => (a E.val : G ⧸ Γ)

noncomputable def cosetCornerCubeSet {d : ℕ} (Γ : Subgroup G)
    (H : Subgroup (Finset (Fin d) → G)) : Set (Option (ProperCubeVertex d) → G ⧸ Γ) :=
  cosetCornerCube Γ '' (H : Set (Finset (Fin d) → G))

theorem cosetCornerCubeSet_unique {d : ℕ} (Γ : Subgroup G)
    (H : Subgroup (Finset (Fin d) → G))
    (hcoordinates : ∀ z ∈ H, ProperUpperFaceCoordinates z) :
    CornerUnique (cosetCornerCubeSet Γ H) := by
  intro x hx y hy hpartial
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨coeff, faces, hproper, horder, hrepr⟩ :=
    hcoordinates (a⁻¹ * b) (H.mul_mem (H.inv_mem ha) hb)
  apply upperFace_coset_missing_top Γ a b coeff faces hproper horder
  · exact hrepr
  · intro E hE
    exact hpartial ⟨E, hE⟩

theorem cosetCornerCubeSet_continuous_reconstruction {d : ℕ}
    (Γ : Subgroup G)
    [TopologicalSpace (G ⧸ Γ)] [T2Space (G ⧸ Γ)]
    (H : Subgroup (Finset (Fin d) → G))
    (hcoordinates : ∀ z ∈ H, ProperUpperFaceCoordinates z)
    (hcompact : IsCompact (cosetCornerCubeSet Γ H)) :
    ∃ R : C(Set.range (fun x : cosetCornerCubeSet Γ H => cornerDelete x.val), G ⧸ Γ),
      ∀ x : cosetCornerCubeSet Γ H,
        R ⟨cornerDelete x.val, ⟨x, rfl⟩⟩ = x.val none := by
  exact compactCorner_continuous_reconstruction (cosetCornerCubeSet Γ H) hcompact
    (cosetCornerCubeSet_unique Γ H hcoordinates)

theorem cosetCornerCubeSet_boundedLipschitz_recipes {d : ℕ} (Γ : Subgroup G)
    [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (H : Subgroup (Finset (Fin d) → G))
    (hcoordinates : ∀ z ∈ H, ProperUpperFaceCoordinates z)
    (hcompact : IsCompact (cosetCornerCubeSet Γ H))
    (A : Set C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ f ∈ A, ∀ x, |f x| ≤ B) (hL : ∀ f ∈ A, LipschitzWith L f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ recipes : Finset (CornerProductRecipe (ProperCubeVertex d) (G ⧸ Γ)),
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ r ∈ recipes, CornerProductRecipe.Bounded r ∧ r.coefficientMass ≤ C) ∧
        (∀ f ∈ A, ∃ r ∈ recipes, ∀ a ∈ H,
          |r.value (cornerDelete (cosetCornerCube Γ a)) - f (a Finset.univ)| < ε) := by
  obtain ⟨recipes, C, hC, hb, ha⟩ := compactCorner_boundedLipschitz_recipes
    (cosetCornerCubeSet Γ H) hcompact (cosetCornerCubeSet_unique Γ H hcoordinates)
    A B L hB hL ε hε
  refine ⟨recipes, C, hC, hb, ?_⟩
  intro f hf
  obtain ⟨r, hr, happrox⟩ := ha f hf
  refine ⟨r, hr, ?_⟩
  intro a ha
  exact happrox (cosetCornerCube Γ a) ⟨a, ha, rfl⟩

end Hindman168
