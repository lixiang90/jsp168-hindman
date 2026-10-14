import Hindman168.AlignmentPolynomialInputShifts
import Mathlib.GroupTheory.Nilpotent

/-! A concrete group of integer-input polynomial arrays. Generators
of degree at most j+1 take values in lower-central level j (Mathlib
starts that series at level zero). Identification with the paper's
finite-dimensional Lie array group and cocompactness remain to prove. -/

namespace Hindman168
open scoped BigOperators Classical

def alignmentPolynomialArrayGenerators (σ G : Type*) [Group G] : Set ((σ → ℤ) → G) :=
  {f | ∃ j : ℕ, ∃ g : G, ∃ p : MvPolynomial σ ℤ,
    g ∈ (⊤ : Subgroup G).lowerCentralSeries j ∧ p.totalDegree ≤ j + 1 ∧
      f = fun u => g ^ MvPolynomial.eval u p}

def alignmentPolynomialArrayGroup (σ G : Type*) [Group G] : Subgroup ((σ → ℤ) → G) :=
  Subgroup.closure (alignmentPolynomialArrayGenerators σ G)

theorem alignmentPolynomialArrayGroup_generator {σ G : Type*} [Group G]
    (j : ℕ) (g : G) (p : MvPolynomial σ ℤ)
    (hg : g ∈ (⊤ : Subgroup G).lowerCentralSeries j) (hp : p.totalDegree ≤ j + 1) :
    (fun u => g ^ MvPolynomial.eval u p) ∈ alignmentPolynomialArrayGroup σ G :=
  Subgroup.subset_closure ⟨j, g, p, hg, hp, rfl⟩

theorem alignmentPolynomialArrayGroup_constant {σ G : Type*} [Group G] (x : G) :
    (fun _ : σ → ℤ => x) ∈ alignmentPolynomialArrayGroup σ G := by
  have h := alignmentPolynomialArrayGroup_generator 0 x (MvPolynomial.C 1 : MvPolynomial σ ℤ)
    (by simp only [Subgroup.lowerCentralSeries_zero, Subgroup.mem_top]) (by simp)
  simpa only [MvPolynomial.eval_C, zpow_one] using h

theorem alignmentPolynomialArrayGroup_model {σ G : Type*} [Fintype σ] [Group G]
    (g x : G) (k : ℤ) (Δ : σ → ℤ) :
    (fun u => g ^ (k + ∑ j, u j * Δ j) * x) ∈ alignmentPolynomialArrayGroup σ G := by
  have h := alignmentPolynomialArrayGroup_generator 0 g (alignmentAffineArrayPolynomial k Δ)
    (by simp only [Subgroup.lowerCentralSeries_zero, Subgroup.mem_top])
    (alignmentAffineArrayPolynomial_degree k Δ)
  have hp : (fun u => g ^ (k + ∑ j, u j * Δ j)) ∈ alignmentPolynomialArrayGroup σ G := by
    simpa only [alignmentAffineArrayPolynomial_eval] using h
  exact (alignmentPolynomialArrayGroup σ G).mul_mem hp (alignmentPolynomialArrayGroup_constant x)

def alignmentPolynomialArrayEvaluation {σ G : Type*} [Group G] (u : σ → ℤ) :
    alignmentPolynomialArrayGroup σ G →* G where
  toFun f := f.val u
  map_one' := rfl
  map_mul' _ _ := rfl

theorem alignmentPolynomialArrayGroup_lowerCentral_bot {σ G : Type*} [Group G]
    (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (alignmentPolynomialArrayGroup σ G)).lowerCentralSeries s = ⊥ := by
  apply le_bot_iff.mp
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  funext u
  have hle : ((⊤ : Subgroup (alignmentPolynomialArrayGroup σ G)).lowerCentralSeries s).map
      (alignmentPolynomialArrayEvaluation u) ≤ (⊤ : Subgroup G).lowerCentralSeries s := by
    rw [Subgroup.map_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono s le_top
  have h := hle (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
  rw [hG] at h
  exact Subgroup.mem_bot.mp h

theorem alignmentPolynomialArrayGroup_nilpotent {σ G : Type*} [Group G]
    (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Group.IsNilpotent (alignmentPolynomialArrayGroup σ G) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s, alignmentPolynomialArrayGroup_lowerCentral_bot s hG⟩

theorem alignmentPolynomialArrayGroup_nilpotencyClass_le {σ G : Type*} [Group G]
    (s : ℕ) (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Group.nilpotencyClass (alignmentPolynomialArrayGroup σ G) ≤ s := by
  letI := alignmentPolynomialArrayGroup_nilpotent (σ := σ) s hG
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (alignmentPolynomialArrayGroup_lowerCentral_bot s hG)

end Hindman168
