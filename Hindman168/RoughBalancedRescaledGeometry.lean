import Hindman168.RoughBalancedBoxGeometry
import Hindman168.RoughResidueBoxGeometry

namespace Hindman168
open scoped Classical

theorem rough_balanced_piece_minimum_side {ι : Type*} (A B : ι → ℤ) (N K : ℕ)
    (hN : 0 < N) (hlen : ∀ j, (2*N*K : ℤ) ≤ B j-A j) (i : ι → Fin N) :
    ∀ j, (2*K : ℤ) ≤ roughBoxUpper A B N i j-roughBoxLower A B N i j := by
  intro j
  have hn : 2*N*K ≤ (B j-A j).toNat := by
    have hh := (hlen j).trans (Int.self_le_toNat (B j-A j))
    exact_mod_cast hh
  have hd : 2*K ≤ (B j-A j).toNat/N :=
    (Nat.le_div_iff_mul_le hN).mpr (by nlinarith [hn])
  have hdz : (2*K : ℤ) ≤ ((B j-A j).toNat/N : ℕ) := by exact_mod_cast hd
  exact hdz.trans (rough_balanced_cut_step (A j) (B j) N (i j).val).1

theorem rough_balanced_rescaled_side_bounds {ι : Type*} (A B : ι → ℤ) (N K : ℕ)
    (hN : 0 < N) (hK : 0 < K) (hlen : ∀ j, (2*N*K : ℤ) ≤ B j-A j)
    (c C Z : ℝ) (hlo : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (hhi : ∀ j, (B j : ℝ)-A j ≤ C*Z) (p : (ι → Fin N) × (ι → Fin K)) :
    let u : ι → ℤ := fun j => (p.2 j).val
    let lo := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
    let hi := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
    ∀ j, (c/(4*N))*(Z/K) ≤ (hi j : ℝ)-lo j ∧
      (hi j : ℝ)-lo j ≤ (4*C/N)*(Z/K) := by
  intro u lo hi
  have hk : (0 : ℤ) < K := by exact_mod_cast hK
  have h2N : ∀ j, (2*N : ℤ) ≤ B j-A j := by
    intro j
    have hkk : (1 : ℤ) ≤ K := by exact_mod_cast hK
    have hn0 : (0 : ℤ) ≤ 2*N := by positivity
    nlinarith [hlen j]
  have hs := rough_balanced_box_scaled_sides A B N hN h2N c C Z hlo hhi p.1
  have hh := rough_residue_box_scaled_side_bounds (roughBoxLower A B N p.1)
    (roughBoxUpper A B N p.1) u K hk
    (rough_balanced_piece_minimum_side A B N K hN hlen p.1)
    (c/(2*N)) (2*C/N) Z
    (fun j => by have h := (hs j).1; convert h using 1; ring)
    (fun j => by have h := (hs j).2; convert h using 1; ring)
  simp only [Int.cast_natCast] at hh
  intro j
  constructor
  · convert (hh j).1 using 1
    ring
  · convert (hh j).2 using 1
    ring

theorem rough_balanced_rescaled_position_bound {ι : Type*} [Fintype ι]
    (A B : ι → ℤ) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (hAB : ∀ j, A j ≤ B j) (C Z : ℝ) (hscale : 1 ≤ Z/K)
    (hA : ∀ j, |(A j : ℝ)| ≤ C*Z) (hB : ∀ j, |(B j : ℝ)| ≤ C*Z)
    (p : (ι → Fin N) × (ι → Fin K)) (y : ι → ℤ)
    (hy : y ∈ Fintype.piFinset (fun j =>
      Finset.Ico
        (roughResidueBoxEndpoint (roughBoxLower A B N p.1) (fun j => (p.2 j).val) K j)
        (roughResidueBoxEndpoint (roughBoxUpper A B N p.1) (fun j => (p.2 j).val) K j))) :
    ∀ j, |(y j : ℝ)| ≤ (C+1)*(Z/K) := by
  have hk : (0 : ℤ) < K := by exact_mod_cast hK
  have hc := rough_balanced_box_contained A B N hN hAB p.1
  have hlo : ∀ j, |(roughBoxLower A B N p.1 j : ℝ)| ≤ C*Z := by
    intro j
    have h1 : (A j : ℝ) ≤ roughBoxLower A B N p.1 j := by exact_mod_cast hc.1 j
    have h2 : (roughBoxLower A B N p.1 j : ℝ) ≤ B j := by
      exact_mod_cast (hc.2.1 j).trans (hc.2.2 j)
    have ha := abs_le.mp (hA j)
    have hb := abs_le.mp (hB j)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hhi : ∀ j, |(roughBoxUpper A B N p.1 j : ℝ)| ≤ C*Z := by
    intro j
    have h1 : (A j : ℝ) ≤ roughBoxUpper A B N p.1 j := by
      exact_mod_cast (hc.1 j).trans (hc.2.1 j)
    have h2 : (roughBoxUpper A B N p.1 j : ℝ) ≤ B j := by exact_mod_cast hc.2.2 j
    have ha := abs_le.mp (hA j)
    have hb := abs_le.mp (hB j)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact rough_residue_box_position_bound _ _ _ K hk
    (fun j => ⟨by positivity, by exact_mod_cast (p.2 j).isLt⟩) C Z hscale hlo hhi y hy

end Hindman168
