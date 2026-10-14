import Hindman168.AffineShearFilteredSection

/-! Actual adapted coordinates with weights in {1,...,s}.  The basis, weights,
and vanishing of every weight-j coordinate on level j+1 are constructed from
the finite filtration, rather than added as coordinate assumptions. -/
namespace Hindman168
open Module

 theorem affineShear_adapted_coordinate_annihilates {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] (b : Basis ι K E) (P : Submodule K E)
    (hspan : Submodule.span K (b '' {i | b i ∈ P}) = P)
    (i : ι) (hi : b i ∉ P) : P ≤ (b.coord i).ker := by
  classical
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  have hne : j ≠ i := by
    intro hji
    exact hi (hji ▸ hj)
  change b.coord i (b j) = 0
  simp [Basis.coord_apply, Ne.symm hne]

 theorem affineShear_adapted_basis_exists {K E : Type*} [Field K]
    [AddCommGroup E] [Module K E] [Module.Finite K E]
    (s : ℕ) (P : ℕ → Submodule K E) (hP : Antitone P)
    (htop : P 1 = ⊤) (hterm : P (s+1) = ⊥) :
    ∃ n : ℕ, ∃ b : Basis (Fin n) K E, ∃ weights : Fin n → ℕ,
      ∀ i, 1 ≤ weights i ∧ weights i ≤ s ∧ b i ∈ P (weights i) ∧
        P (weights i+1) ≤ (b.coord i).ker := by
  classical
  obtain ⟨n, b, hb⟩ := split_integer_flag_basis_exists (s+2)
    (fun j : Fin (s+2) => P j.val) (fun _ _ hij => hP hij)
    (fun j => (P j.val).exists_isCompl)
  have hex (i : Fin n) : ∃ w : ℕ, 1 ≤ w ∧ w ≤ s ∧ b i ∈ P w ∧
      P (w+1) ≤ (b.coord i).ker := by
    let S := (Finset.range (s+2)).filter (fun j => b i ∈ P j)
    have h1 : 1 ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), by rw [htop]; trivial⟩
    have hnon : S.Nonempty := ⟨1, h1⟩
    let w := S.max' hnon
    have hwS : w ∈ S := Finset.max'_mem S hnon
    have hw : b i ∈ P w := (Finset.mem_filter.mp hwS).2
    have hwlt : w < s+2 := Finset.mem_range.mp (Finset.mem_filter.mp hwS).1
    have hlow : 1 ≤ w := Finset.le_max' S 1 h1
    have hne : w ≠ s+1 := by
      intro he
      have hz : b i = 0 := by simpa only [he, hterm, Submodule.mem_bot] using hw
      exact b.ne_zero i hz
    have hhigh : w ≤ s := by omega
    have hnot : b i ∉ P (w+1) := by
      intro hnext
      have hmem : w+1 ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hnext⟩
      have hle := Finset.le_max' S (w+1) hmem
      change w+1 ≤ w at hle
      omega
    refine ⟨w, hlow, hhigh, hw, ?_⟩
    exact affineShear_adapted_coordinate_annihilates b (P (w+1))
      (hb ⟨w+1, by omega⟩) i hnot
  choose weights hw using hex
  exact ⟨n, b, weights, hw⟩

end Hindman168
