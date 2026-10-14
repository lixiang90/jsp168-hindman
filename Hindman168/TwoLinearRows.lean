import Hindman168.PrimitiveLinearRows
import Mathlib.Algebra.Group.Prod

/-!
# Actual independent two-row counts

A unit two-column minor gives an explicit preimage for every pair of row
values. Reduction of the second value to a smaller prime power remains
surjective. The original uniform base law therefore has simultaneous
zero-row probability exactly p^(-A-B), including zero exponents.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem linearRowAddHom_single {R : Type*} [CommRing R] {d : ℕ}
    (c : Fin d → R) (j : Fin d) (s : R) :
    linearRowAddHom c (Pi.single j s) = c j * s := by
  simp [linearRowAddHom, Pi.single_apply]

noncomputable def twoRowAddHom {R : Type*} [CommRing R] {d : ℕ}
    (c e : Fin d → R) : (Fin d → R) →+ R × R :=
  (linearRowAddHom c).prod (linearRowAddHom e)

theorem twoRowAddHom_surjective_of_unit_minor {R : Type*} [CommRing R] {d : ℕ}
    (c e : Fin d → R) (j k : Fin d)
    (hminor : IsUnit (c j * e k - c k * e j)) :
    Function.Surjective (twoRowAddHom c e) := by
  classical
  obtain ⟨u, hu⟩ := hminor
  intro y
  let v : R := ↑(u⁻¹)
  let s : R := v * (e k * y.1 - c k * y.2)
  let t : R := v * (c j * y.2 - e j * y.1)
  refine ⟨Pi.single j s + Pi.single k t, ?_⟩
  apply Prod.ext
  · change linearRowAddHom c (Pi.single j s + Pi.single k t) = y.1
    rw [map_add, linearRowAddHom_single, linearRowAddHom_single]
    calc
      c j * s + c k * t = v * (c j * e k - c k * e j) * y.1 := by dsimp [s, t]; ring
      _ = y.1 := by rw [← hu]; simp [v]
  · change linearRowAddHom e (Pi.single j s + Pi.single k t) = y.2
    rw [map_add, linearRowAddHom_single, linearRowAddHom_single]
    calc
      e j * s + e k * t = v * (c j * e k - c k * e j) * y.2 := by dsimp [s, t]; ring
      _ = y.2 := by rw [← hu]; simp [v]

noncomputable def reducedTwoRowAddHom {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (c e : Fin d → R) (r : R →+* S) : (Fin d → R) →+ R × S :=
  (linearRowAddHom c).prod (r.toAddMonoidHom.comp (linearRowAddHom e))

theorem reducedTwoRowAddHom_surjective {R S : Type*} [CommRing R] [CommRing S] {d : ℕ}
    (c e : Fin d → R) (r : R →+* S) (hr : Function.Surjective r)
    (hrows : Function.Surjective (twoRowAddHom c e)) :
    Function.Surjective (reducedTwoRowAddHom c e r) := by
  intro y
  obtain ⟨z, hz⟩ := hr y.2
  obtain ⟨x, hx⟩ := hrows (y.1, z)
  refine ⟨x, ?_⟩
  have hc : linearRowAddHom c x = y.1 := congrArg Prod.fst hx
  have he : linearRowAddHom e x = z := congrArg Prod.snd hx
  apply Prod.ext
  · exact hc
  · change r (linearRowAddHom e x) = y.2
    rw [he, hz]

theorem primePower_twoRow_surjective {p d A : ℕ} (hp : p.Prime)
    (c e : Fin d → ℤ) (j k : Fin d)
    (hminor : ((c j * e k - c k * e j : ℤ) : ZMod p) ≠ 0) :
    Function.Surjective (twoRowAddHom (fun i => (c i : ZMod (p ^ A)))
      (fun i => (e i : ZMod (p ^ A)))) := by
  apply twoRowAddHom_surjective_of_unit_minor _ _ j k
  simpa only [Int.cast_sub, Int.cast_mul] using
    integer_coefficient_unit_primePower hp A (c j * e k - c k * e j) hminor

theorem primePower_reduced_twoRow_zero_mass {p d A B : ℕ} [NeZero p]
    (hp : p.Prime) (hBA : B ≤ A) (c e : Fin d → ℤ) (j k : Fin d)
    (hminor : ((c j * e k - c k * e j : ℤ) : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => reducedTwoRowAddHom (fun i => (c i : ZMod (p ^ A)))
        (fun i => (e i : ZMod (p ^ A)))
        (ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))) x = 0) =
      ((p ^ (A + B) : ℕ) : ℝ)⁻¹ := by
  let r := ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
  let f := reducedTwoRowAddHom (fun i => (c i : ZMod (p ^ A)))
    (fun i => (e i : ZMod (p ^ A))) r
  have hf : Function.Surjective f := reducedTwoRowAddHom_surjective _ _ r
    (ZMod.castHom_surjective _) (primePower_twoRow_surjective hp c e j k hminor)
  have hpush := uniformFintypeMass_addGroup_push f hf
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod (p ^ A))) f
    (fun y : ZMod (p ^ A) × ZMod (p ^ B) => y = 0)
  rw [hpush, uniformFintypeMass_event_eq, Fintype.card_prod, ZMod.card, ZMod.card,
    ← pow_add] at hmap
  exact hmap.symm

theorem primePower_twoRow_divisibility_mass {p d A B : ℕ} [NeZero p]
    (hp : p.Prime) (hBA : B ≤ A) (c e : Fin d → ℤ) (j k : Fin d)
    (hminor : ((c j * e k - c k * e j : ℤ) : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x = 0 ∧
        ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
          (linearRowAddHom (fun i => (e i : ZMod (p ^ A))) x) = 0) =
      ((p ^ (A + B) : ℕ) : ℝ)⁻¹ := by
  have h := primePower_reduced_twoRow_zero_mass hp hBA c e j k hminor
  change event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
    (fun x => (linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x,
      ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
        (linearRowAddHom (fun i => (e i : ZMod (p ^ A))) x)) = 0) = _ at h
  simpa only [Prod.mk_eq_zero] using h

noncomputable def doublyReducedTwoRowAddHom {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] {d : ℕ}
    (c e : Fin d → R) (r : R →+* S) (s : R →+* T) : (Fin d → R) →+ S × T :=
  (r.toAddMonoidHom.comp (linearRowAddHom c)).prod
    (s.toAddMonoidHom.comp (linearRowAddHom e))

theorem doublyReducedTwoRowAddHom_surjective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] {d : ℕ}
    (c e : Fin d → R) (r : R →+* S) (s : R →+* T)
    (hr : Function.Surjective r) (hs : Function.Surjective s)
    (hrows : Function.Surjective (twoRowAddHom c e)) :
    Function.Surjective (doublyReducedTwoRowAddHom c e r s) := by
  intro y
  obtain ⟨z, hz⟩ := hr y.1
  obtain ⟨v, hv⟩ := hs y.2
  obtain ⟨x, hx⟩ := hrows (z, v)
  refine ⟨x, ?_⟩
  have hc : linearRowAddHom c x = z := congrArg Prod.fst hx
  have he : linearRowAddHom e x = v := congrArg Prod.snd hx
  apply Prod.ext
  · change r (linearRowAddHom c x) = y.1
    rw [hc, hz]
  · change s (linearRowAddHom e x) = y.2
    rw [he, hv]

theorem primePower_twoRow_reduced_divisibility_mass {p d A B C : ℕ} [NeZero p]
    (hp : p.Prime) (hBA : B ≤ A) (hCA : C ≤ A) (c e : Fin d → ℤ) (j k : Fin d)
    (hminor : ((c j * e k - c k * e j : ℤ) : ZMod p) ≠ 0) :
    event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
      (fun x => ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
          (linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x) = 0 ∧
        ZMod.castHom (pow_dvd_pow p hCA) (ZMod (p ^ C))
          (linearRowAddHom (fun i => (e i : ZMod (p ^ A))) x) = 0) =
      ((p ^ (B + C) : ℕ) : ℝ)⁻¹ := by
  let r := ZMod.castHom (pow_dvd_pow p hBA) (ZMod (p ^ B))
  let s := ZMod.castHom (pow_dvd_pow p hCA) (ZMod (p ^ C))
  let f := doublyReducedTwoRowAddHom (fun i => (c i : ZMod (p ^ A)))
    (fun i => (e i : ZMod (p ^ A))) r s
  have hf : Function.Surjective f := doublyReducedTwoRowAddHom_surjective _ _ r s
    (ZMod.castHom_surjective _) (ZMod.castHom_surjective _)
    (primePower_twoRow_surjective hp c e j k hminor)
  have hpush := uniformFintypeMass_addGroup_push f hf
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod (p ^ A))) f
    (fun y : ZMod (p ^ B) × ZMod (p ^ C) => y = 0)
  rw [hpush, uniformFintypeMass_event_eq, Fintype.card_prod, ZMod.card, ZMod.card,
    ← pow_add] at hmap
  have h := hmap.symm
  change event (uniformFintypeMass (Fin d → ZMod (p ^ A)))
    (fun x => (r (linearRowAddHom (fun i => (c i : ZMod (p ^ A))) x),
      s (linearRowAddHom (fun i => (e i : ZMod (p ^ A))) x)) = 0) = _ at h
  simpa only [Prod.mk_eq_zero] using h

end Hindman168
