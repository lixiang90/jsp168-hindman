import Hindman168.BinaryDyadicCutoffDiscard
import Hindman168.DyadicHarmonicConditioning

namespace Hindman168
open scoped Classical

noncomputable def binaryDyadicResidueWindow (L x : ℕ) : Finset ℕ :=
  residueWindow (2 ^ Nat.log2 x : ℕ) (2 * (2 ^ Nat.log2 x : ℕ)) L (x % L)

theorem binaryDyadicResidueWindow_mem {L x p : ℕ} (hp : 0 < p) :
    p ∈ binaryDyadicResidueWindow L x ↔
      Nat.log2 p = Nat.log2 x ∧ p % L = x % L := by
  rw [binaryDyadicResidueWindow, mem_residueWindow]
  constructor
  · rintro ⟨hlo, hhi, hr⟩
    have hlo' : 2 ^ Nat.log2 x ≤ p := by exact_mod_cast hlo
    have hhi' : p < 2 ^ (Nat.log2 x + 1) := by
      rw [pow_succ]
      have hh : p < 2 * 2 ^ Nat.log2 x := by exact_mod_cast hhi
      simpa only [mul_comm] using hh
    exact ⟨(Nat.log2_eq_iff hp.ne').mpr ⟨hlo', hhi'⟩, hr⟩
  · rintro ⟨he, hr⟩
    rw [← he]
    refine ⟨?_, ?_, hr⟩
    · exact_mod_cast Nat.log2_self_le hp.ne'
    · have hh : p < 2 * 2 ^ Nat.log2 p := by
        simpa only [pow_succ, mul_comm] using (Nat.lt_log2_self (n := p))
      exact_mod_cast hh

theorem binaryDyadicResidueWindow_anchor {L x : ℕ} (hx : 0 < x) :
    x ∈ binaryDyadicResidueWindow L x :=
  (binaryDyadicResidueWindow_mem hx).mpr ⟨rfl, rfl⟩

theorem binaryDyadicResidueWindow_subset {X W L x : ℕ}
    (hgood : binaryDyadicCutoffGood X x) (hWL : W ∣ L) (hx : Nat.Coprime x W) :
    binaryDyadicResidueWindow L x ⊆ harmonicWindow X W := by
  apply dyadic_residueWindow_subset
  · exact_mod_cast hgood.1
  · exact_mod_cast hgood.2
  · exact hWL
  · exact (residue_coprime_iff W L (x % L) x hWL rfl).mp hx

end Hindman168
