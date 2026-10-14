import Hindman168.GapMultiples
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# Actual finite polynomial requirements for the gap length

All polynomial values on the full finite Cartesian prime pool are included.
Only zero values are omitted, as required by the master-scales lemma.
The common modulus and all earlier gap lengths are included separately.
-/

namespace Hindman168

open scoped BigOperators

noncomputable def polynomialPoolValues {m : ℕ}
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact (D ×ˢ Fintype.piFinset (fun _ : Fin m => P)).image
    (fun x => (MvPolynomial.eval (fun i => (x.2 i : ℤ)) x.1).natAbs)

theorem polynomialPoolValues_mem {m : ℕ} {D : Finset (MvPolynomial (Fin m) ℤ)}
    {P : Finset ℕ} {d : MvPolynomial (Fin m) ℤ} {p : Fin m → ℕ}
    (hd : d ∈ D) (hp : ∀ i, p i ∈ P) :
    (MvPolynomial.eval (fun i => (p i : ℤ)) d).natAbs ∈ polynomialPoolValues D P := by
  classical
  exact Finset.mem_image.mpr ⟨(d, p),
    Finset.mem_product.mpr ⟨hd, Fintype.mem_piFinset.mpr hp⟩, rfl⟩

noncomputable def polynomialGapRequirements {m : ℕ} (M : ℕ) (earlier : Finset ℕ)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) : Finset ℕ := by
  classical
  exact insert M (earlier ∪ ((polynomialPoolValues D P).filter (0 < ·)).image (M * ·))

theorem polynomialGapRequirements_pos {m M : ℕ} {earlier : Finset ℕ}
    (hM : 0 < M) (he : ∀ n ∈ earlier, 0 < n)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) :
    ∀ n ∈ polynomialGapRequirements M earlier D P, 0 < n := by
  classical
  intro n hn
  rcases Finset.mem_insert.mp hn with rfl | hn
  · exact hM
  rcases Finset.mem_union.mp hn with hn | hn
  · exact he n hn
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
  exact Nat.mul_pos hM (Finset.mem_filter.mp hv).2

noncomputable def polynomialGap {m : ℕ} (M : ℕ) (earlier : Finset ℕ)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) (B w : ℕ) : ℕ :=
  gapMultiple (polynomialGapRequirements M earlier D P) B w

theorem polynomialGap_pos {m M : ℕ} {earlier : Finset ℕ}
    (hM : 0 < M) (he : ∀ n ∈ earlier, 0 < n)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) (B w : ℕ) :
    0 < polynomialGap M earlier D P B w :=
  gapMultiple_pos (polynomialGapRequirements_pos hM he D P) B w

theorem polynomialGap_modulus_dvd {m : ℕ} (M : ℕ) (earlier : Finset ℕ)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) (B w : ℕ) :
    M ∣ polynomialGap M earlier D P B w := by
  classical
  exact gapMultiple_dvd (Finset.mem_insert_self _ _) B w

theorem polynomialGap_earlier_dvd {m : ℕ} (M : ℕ) {earlier : Finset ℕ}
    {n : ℕ} (hn : n ∈ earlier) (D : Finset (MvPolynomial (Fin m) ℤ))
    (P : Finset ℕ) (B w : ℕ) : n ∣ polynomialGap M earlier D P B w := by
  classical
  exact gapMultiple_dvd (Finset.mem_insert_of_mem (Finset.mem_union_left _ hn)) B w

theorem polynomialGap_value_dvd {m : ℕ} (M : ℕ) (earlier : Finset ℕ)
    {D : Finset (MvPolynomial (Fin m) ℤ)} {P : Finset ℕ}
    {d : MvPolynomial (Fin m) ℤ} {p : Fin m → ℕ}
    (hd : d ∈ D) (hp : ∀ i, p i ∈ P)
    (hv : MvPolynomial.eval (fun i => (p i : ℤ)) d ≠ 0) (B w : ℕ) :
    M * (MvPolynomial.eval (fun i => (p i : ℤ)) d).natAbs ∣
      polynomialGap M earlier D P B w := by
  classical
  apply gapMultiple_dvd (B := B) (w := w)
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨_, Finset.mem_filter.mpr ⟨polynomialPoolValues_mem hd hp, ?_⟩, rfl⟩
  exact Nat.pos_of_ne_zero (by simpa using hv)

theorem polynomialGap_lower {m M : ℕ} {earlier : Finset ℕ}
    (hM : 0 < M) (he : ∀ n ∈ earlier, 0 < n)
    (D : Finset (MvPolynomial (Fin m) ℤ)) (P : Finset ℕ) (B w : ℕ) :
    w * B ^ w ≤ polynomialGap M earlier D P B w :=
  gapMultiple_lower (polynomialGapRequirements_pos hM he D P) B w

end Hindman168
