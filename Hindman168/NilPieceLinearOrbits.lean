import Hindman168.NilPieceCubeGeometry
import Hindman168.NilUpperFaceRootRecipes

/-! Actual piecewise linear nilorbits on residue classes. Finite uniform
root recipes are indexed and chosen for arbitrarily many pieces; the
same finite family works for unrestricted translating elements/basepoints. -/

namespace Hindman168
open scoped BigOperators Classical
open NNReal

variable {G P : Type*} [Group G] {d : ℕ}

noncomputable def pieceLinearOrbit (Γ : Subgroup G) (M : ℕ) (g x : P → G)
    (p : P) (y : ℤ) : G ⧸ Γ := (g p ^ (y / (M : ℤ)) * x p : G ⧸ Γ)

theorem zeroPrimeRecipeVertex_quotient (M : ℕ) (hM : 0 < M) (y : ℤ)
    (z : Fin d × Bool → ℤ) (S : CubeVertex d) :
    zeroPrimeRecipeVertex M y z S / (M : ℤ) =
      y / (M : ℤ) + ∑ j ∈ S.val, (z (j, true) - z (j, false)) := by
  have hm : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  exact Int.add_mul_ediv_left y _ hm

theorem pieceLinearOrbit_zeroPrimeVertex (Γ : Subgroup G) (M : ℕ) (hM : 0 < M)
    (g x : P → G) (p : P) (y : ℤ) (z : Fin d × Bool → ℤ) (S : CubeVertex d) :
    pieceLinearOrbit Γ M g x p (zeroPrimeRecipeVertex M y z S) =
      (g p ^ (y / (M : ℤ) + ∑ j ∈ S.val, (z (j, true) - z (j, false))) * x p : G ⧸ Γ) := by
  simp only [pieceLinearOrbit, zeroPrimeRecipeVertex_quotient M hM y z S]

theorem upperFaceCubeGroup_piece_linear_recipe_family (F : ℕ → Subgroup G)
    (hF : CubeGroupFiltration F) (htop : F d = ⊥) (hzero : F 0 = ⊤) (hone : F 1 = ⊤)
    (Γ : Subgroup G) [MetricSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hcompact : IsCompact (cosetCornerCubeSet Γ (upperFaceCubeGroup F d)))
    (obs : P → C(G ⧸ Γ, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ p q, |obs p q| ≤ B) (hL : ∀ p, LipschitzWith L (obs p))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ recipes : Fin N → CornerProductRecipe (CubeVertex d) (G ⧸ Γ),
      ∃ chooseRecipe : P → Fin N, ∃ C : ℝ, 0 ≤ C ∧
      (∀ r, CornerProductRecipe.Bounded (recipes r) ∧ (recipes r).coefficientMass ≤ C) ∧
      ∀ p, ∀ g x : G, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
        |(recipes (chooseRecipe p)).value
          (fun E => (g ^ (b₀ + ∑ j ∈ E.val, b j) * x : G ⧸ Γ)) - obs p (g ^ b₀ * x)| < δ := by
  obtain ⟨rs, C, hC, hb, ha⟩ := upperFaceCubeGroup_linear_root_recipes F hF htop hzero hone Γ
    hcompact (Set.range obs) B L (by rintro f ⟨p, rfl⟩; exact hB p)
    (by rintro f ⟨p, rfl⟩; exact hL p) δ hδ
  have hchoose (p : P) := ha (obs p) ⟨p, rfl⟩
  choose selected hselected happrox using hchoose
  have hget (p : P) : ∃ i : Fin rs.toList.length, rs.toList.get i = selected p :=
    List.mem_iff_get.mp (Finset.mem_toList.mpr (hselected p))
  choose index hindex using hget
  refine ⟨rs.toList.length, rs.toList.get, index, C, hC, ?_, ?_⟩
  · intro i
    exact hb _ (Finset.mem_toList.mp (List.get_mem _ _))
  · intro p g x b₀ b
    rw [hindex p]
    exact happrox p g x b₀ b

theorem pieceRecipeCubeSum_linear_good_root {N : ℕ}
    (Γ : Subgroup G) [TopologicalSpace (G ⧸ Γ)]
    (recipes : Fin N → CornerProductRecipe (CubeVertex d) (G ⧸ Γ))
    (chooseRecipe : (ℤ × ℤ) → Fin N) (obs : (ℤ × ℤ) → C(G ⧸ Γ, ℝ))
    (g x : (ℤ × ℤ) → G) (R J M : ℕ) (hR : 0 < R) (hM : 0 < M) (hd : 0 < d)
    (δ : ℝ) (ha : ∀ p, ∀ b₀ : ℤ, ∀ b : Fin d → ℤ,
      |(recipes (chooseRecipe p)).value
        (fun E => (g p ^ (b₀ + ∑ j ∈ E.val, b j) * x p : G ⧸ Γ)) - obs p (g p ^ b₀ * x p)| ≤ δ)
    (y : ℤ) (hy : intervalInteriorRoot R (zeroPrimeCubeMargin d R J M) y)
    (z : Fin d × Bool → ℤ) (hz : z ∈ (zeroPrimeRecipeShiftMass d R J M).support) :
    |pieceRecipeCubeSum recipes (intervalResiduePiece R M) chooseRecipe
      (pieceLinearOrbit Γ M g x) (zeroPrimeRecipeVertex M y z) -
      obs (intervalResiduePiece R M y) (pieceLinearOrbit Γ M g x (intervalResiduePiece R M y) y)| ≤ δ := by
  letI : Nonempty (CubeVertex d) := cubeVertex_nonempty_of_pos hd
  rw [pieceRecipeCubeSum_on_piece recipes (intervalResiduePiece R M) chooseRecipe
    (pieceLinearOrbit Γ M g x) (intervalResiduePiece R M y) _
    (fun S => zeroPrimeRecipeVertex_piece_stable R J M hR y hy z hz S)]
  simpa only [pieceLinearOrbit, zeroPrimeRecipeVertex_quotient M hM y z] using
    ha (intervalResiduePiece R M y) (y / (M : ℤ)) (fun j => z (j, true) - z (j, false))

end Hindman168
