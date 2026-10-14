import Hindman168.PolynomialRowDirectionCatalog

/-! Injective coefficient maps retain actual anchors, supports and pair minors. -/

namespace Hindman168

open scoped BigOperators Classical

theorem polynomialRowMinor_map {R S : Type*} [CommRing R] [CommRing S]
    {c : ℕ} (φ : R →+* S) (A B : Fin c → R) (j k : Fin c) :
    polynomialRowMinor (fun i => φ (A i)) (fun i => φ (B i)) j k =
      φ (polynomialRowMinor A B j k) := by
  simp [polynomialRowMinor]

noncomputable def PolynomialRowFamily.mapCoefficients {R S : Type*}
    [CommRing R] [CommRing S] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (φ : R →+* S) (hi : Function.Injective φ) :
    PolynomialRowFamily S r m where
  row i k := φ (F.row i k)
  anchor := F.anchor
  anchor_ne_zero i := fun hz => F.anchor_ne_zero i (hi (by simpa only [map_zero] using hz))
  pair_minor i l hl := by
    obtain ⟨j, k, hjk⟩ := F.pair_minor i l hl
    refine ⟨j, k, ?_⟩
    rw [polynomialRowMinor_map]
    intro hz
    exact hjk (hi (by simpa only [map_zero] using hz))

theorem PolynomialRowFamily.mapCoefficients_support_iff {R S : Type*}
    [CommRing R] [CommRing S] {r m : ℕ}
    (F : PolynomialRowFamily R r m) (φ : R →+* S) (hi : Function.Injective φ)
    (i : Fin r) (k : Fin (m + 1)) :
    (F.mapCoefficients φ hi).row i k ≠ 0 ↔ F.row i k ≠ 0 := by
  change φ (F.row i k) ≠ 0 ↔ F.row i k ≠ 0
  rw [← map_zero φ, hi.ne_iff]

end Hindman168
