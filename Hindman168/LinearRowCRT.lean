import Hindman168.UniformCRT
import Hindman168.PrimePowerRowSystems

/-!
# CRT factorization of actual normalized linear-row counts

Each row may require a smaller divisor of each local base modulus. The
actual global row congruences are equivalent to all the corresponding
local row congruences. The uniform vector law and the normalization both
factor exactly. No desired independence is added as a hypothesis.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem linearRowAddHom_int_map {R S : Type*} [CommRing R] [CommRing S]
    {d : ℕ} (c : Fin d → ℤ) (r : R →+* S) (x : Fin d → R) :
    r (linearRowAddHom (fun j => (c j : R)) x) =
      linearRowAddHom (fun j => (c j : S)) (fun j => r (x j)) := by
  change r (∑ j, (c j : R) * x j) = ∑ j, (c j : S) * r (x j)
  rw [map_sum]
  simp only [map_mul, map_intCast]

noncomputable def residueRowSystem (K q d : ℕ) (s : Fin q → ℕ)
    (hs : ∀ u, s u ∣ K) (c : Fin q → Fin d → ℤ) :
    (Fin d → ZMod K) →+ (∀ u : Fin q, ZMod (s u)) where
  toFun x u := ZMod.castHom (hs u) (ZMod (s u))
    (linearRowAddHom (fun j => (c u j : ZMod K)) x)
  map_zero' := by
    funext u
    change ZMod.castHom (hs u) (ZMod (s u)) (linearRowAddHom _ 0) = 0
    rw [map_zero, map_zero]
  map_add' x y := by
    funext u
    change ZMod.castHom (hs u) (ZMod (s u)) (linearRowAddHom _ (x + y)) = _
    rw [map_add, map_add]
    rfl

theorem residueRowSystem_zero_iff (K q d : ℕ) (s : Fin q → ℕ)
    (hs : ∀ u, s u ∣ K) (c : Fin q → Fin d → ℤ) (x : Fin d → ZMod K) :
    residueRowSystem K q d s hs c x = 0 ↔
      ∀ u, ZMod.castHom (hs u) (ZMod (s u))
        (linearRowAddHom (fun j => (c u j : ZMod K)) x) = 0 :=
  ⟨fun h u => congrFun h u, fun h => funext h⟩

theorem zmod_prod_zero_iff {ι : Type*} [Fintype ι]
    (b : ι → ℕ) (hc : Pairwise (fun i j => (b i).Coprime (b j)))
    (y : ZMod (∏ i, b i)) :
    y = 0 ↔ ∀ i, ZMod.castHom (Finset.dvd_prod_of_mem b (Finset.mem_univ i)) (ZMod (b i)) y = 0 := by
  constructor
  · intro h i
    rw [h, map_zero]
  · intro h
    apply (ZMod.prodEquivPi b hc).injective
    funext i
    simpa only [ZMod.prodEquivPi_apply, map_zero, Pi.zero_apply] using h i

theorem crt_row_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m b : ι → ℕ) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (hb : ∀ i, b i ∣ m i) (d : ℕ) (c : Fin d → ℤ)
    (x : Fin d → ZMod (∏ i, m i)) (i : ι) :
    ZMod.castHom (Finset.dvd_prod_of_mem b (Finset.mem_univ i)) (ZMod (b i))
      (ZMod.castHom (Finset.prod_dvd_prod_of_dvd b m (fun j _ => hb j)) (ZMod (∏ j, b j))
        (linearRowAddHom (fun j => (c j : ZMod (∏ i, m i))) x)) =
      ZMod.castHom (hb i) (ZMod (b i))
        (linearRowAddHom (fun j => (c j : ZMod (m i))) (crtVectorAddEquiv m hc d x i)) := by
  let r := ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))
  have hv : crtVectorAddEquiv m hc d x i = fun j => r (x j) := by
    funext j
    exact crtVectorAddEquiv_apply m hc d x i j
  rw [hv, ← linearRowAddHom_int_map c r x]
  have hh : (ZMod.castHom (Finset.dvd_prod_of_mem b (Finset.mem_univ i)) (ZMod (b i))).comp
      (ZMod.castHom (Finset.prod_dvd_prod_of_dvd b m (fun j _ => hb j)) (ZMod (∏ j, b j))) =
      (ZMod.castHom (hb i) (ZMod (b i))).comp r := Subsingleton.elim _ _
  exact RingHom.congr_fun hh _

theorem residueRowSystem_crt_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (q d : ℕ) (b : ι → Fin q → ℕ) (hb : ∀ i u, b i u ∣ m i)
    (c : Fin q → Fin d → ℤ) (x : Fin d → ZMod (∏ i, m i)) :
    residueRowSystem (∏ i, m i) q d (fun u => ∏ i, b i u)
        (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hb i u)) c x = 0 ↔
      ∀ i, residueRowSystem (m i) q d (b i) (hb i) c (crtVectorAddEquiv m hc d x i) = 0 := by
  have hcop (u : Fin q) : Pairwise (fun i j => (b i u).Coprime (b j u)) := by
    intro i j hij
    exact Nat.Coprime.of_dvd (hb i u) (hb j u) (hc hij)
  rw [residueRowSystem_zero_iff]
  constructor
  · intro h i
    apply (residueRowSystem_zero_iff _ _ _ _ _ _ _).mpr
    intro u
    have hz := congrArg (ZMod.castHom
      (Finset.dvd_prod_of_mem (fun i => b i u) (Finset.mem_univ i)) (ZMod (b i u))) (h u)
    rw [map_zero, crt_row_projection m (fun i => b i u) hc (fun i => hb i u) d (c u) x i] at hz
    exact hz
  · intro h u
    apply (zmod_prod_zero_iff (fun i => b i u) (hcop u) _).mpr
    intro i
    rw [crt_row_projection m (fun i => b i u) hc (fun i => hb i u) d (c u) x i]
    exact (residueRowSystem_zero_iff _ _ _ _ _ _ _).mp (h i) u

theorem residueRowSystem_crt_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (q d : ℕ) (b : ι → Fin q → ℕ) (hb : ∀ i u, b i u ∣ m i)
    (c : Fin q → Fin d → ℤ) :
    event (uniformFintypeMass (Fin d → ZMod (∏ i, m i)))
      (fun x => residueRowSystem (∏ i, m i) q d (fun u => ∏ i, b i u)
        (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hb i u)) c x = 0) =
      ∏ i, event (uniformFintypeMass (Fin d → ZMod (m i)))
        (fun x => residueRowSystem (m i) q d (b i) (hb i) c x = 0) := by
  have hE : (fun x => residueRowSystem (∏ i, m i) q d (fun u => ∏ i, b i u)
      (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hb i u)) c x = 0) =
      (fun x => ∀ i, residueRowSystem (m i) q d (b i) (hb i) c (crtVectorAddEquiv m hc d x i) = 0) := by
    funext x
    exact propext (residueRowSystem_crt_zero_iff m hc q d b hb c x)
  rw [hE]
  exact crtVector_event_factorization m hc d (fun i x => residueRowSystem (m i) q d (b i) (hb i) c x = 0)

theorem residueRowSystem_normalized_crt_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [NeZero (∏ i, m i)] [∀ i, NeZero (m i)]
    (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (q d : ℕ) (b : ι → Fin q → ℕ) (hb : ∀ i u, b i u ∣ m i)
    (c : Fin q → Fin d → ℤ) :
    ((∏ u, ∏ i, b i u : ℕ) : ℝ) *
      event (uniformFintypeMass (Fin d → ZMod (∏ i, m i)))
        (fun x => residueRowSystem (∏ i, m i) q d (fun u => ∏ i, b i u)
          (fun u => Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hb i u)) c x = 0) =
      ∏ i, (((∏ u, b i u : ℕ) : ℝ) *
        event (uniformFintypeMass (Fin d → ZMod (m i)))
          (fun x => residueRowSystem (m i) q d (b i) (hb i) c x = 0)) := by
  rw [residueRowSystem_crt_mass m hc q d b hb c, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm, Nat.cast_prod]

end Hindman168
