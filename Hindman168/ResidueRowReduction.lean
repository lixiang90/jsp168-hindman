import Hindman168.LinearRowCRT

/-!
# Uniform reduction of row systems to a divisor modulus

Reducing every coordinate of a uniform residue vector gives the actual
uniform vector on the quotient. Integer linear rows commute with this
reduction. Thus local normalized counts are independent of the chosen
base exponent once it dominates all row exponents.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def residueVectorReduction (K Q d : ℕ) (h : Q ∣ K) :
    (Fin d → ZMod K) →+ (Fin d → ZMod Q) where
  toFun x j := ZMod.castHom h (ZMod Q) (x j)
  map_zero' := by funext j; exact map_zero _
  map_add' x y := by funext j; exact map_add _ (x j) (y j)

theorem residueVectorReduction_surjective (K Q d : ℕ) (h : Q ∣ K) :
    Function.Surjective (residueVectorReduction K Q d h) := by
  intro y
  have hz (j : Fin d) := ZMod.castHom_surjective h (y j)
  refine ⟨fun j => Classical.choose (hz j), ?_⟩
  funext j
  exact Classical.choose_spec (hz j)

theorem uniformFintypeMass_residueVectorReduction (K Q d : ℕ) [NeZero K] [NeZero Q] (h : Q ∣ K) :
    (uniformFintypeMass (Fin d → ZMod K)).mapDomain (residueVectorReduction K Q d h) =
      uniformFintypeMass (Fin d → ZMod Q) :=
  uniformFintypeMass_addGroup_push _ (residueVectorReduction_surjective K Q d h)

theorem residueRowSystem_reduction (K Q q d : ℕ) (h : Q ∣ K)
    (s : Fin q → ℕ) (hs : ∀ u, s u ∣ Q) (c : Fin q → Fin d → ℤ) (x : Fin d → ZMod K) :
    residueRowSystem K q d s (fun u => (hs u).trans h) c x =
      residueRowSystem Q q d s hs c (residueVectorReduction K Q d h x) := by
  funext u
  let r := ZMod.castHom h (ZMod Q)
  have hv : residueVectorReduction K Q d h x = fun j => r (x j) := rfl
  change ZMod.castHom ((hs u).trans h) (ZMod (s u))
      (linearRowAddHom (fun j => (c u j : ZMod K)) x) =
    ZMod.castHom (hs u) (ZMod (s u))
      (linearRowAddHom (fun j => (c u j : ZMod Q)) (residueVectorReduction K Q d h x))
  rw [hv, ← linearRowAddHom_int_map (c u) r x]
  have hh : ZMod.castHom ((hs u).trans h) (ZMod (s u)) =
      (ZMod.castHom (hs u) (ZMod (s u))).comp r := Subsingleton.elim _ _
  exact RingHom.congr_fun hh _

theorem residueRowSystem_mass_reduction (K Q q d : ℕ) [NeZero K] [NeZero Q] (h : Q ∣ K)
    (s : Fin q → ℕ) (hs : ∀ u, s u ∣ Q) (c : Fin q → Fin d → ℤ) :
    event (uniformFintypeMass (Fin d → ZMod K))
      (fun x => residueRowSystem K q d s (fun u => (hs u).trans h) c x = 0) =
      event (uniformFintypeMass (Fin d → ZMod Q))
        (fun x => residueRowSystem Q q d s hs c x = 0) := by
  have hmap := event_map (uniformFintypeMass (Fin d → ZMod K))
    (residueVectorReduction K Q d h) (fun y => residueRowSystem Q q d s hs c y = 0)
  rw [uniformFintypeMass_residueVectorReduction] at hmap
  have hE : (fun x => residueRowSystem K q d s (fun u => (hs u).trans h) c x = 0) =
      (fun x => residueRowSystem Q q d s hs c (residueVectorReduction K Q d h x) = 0) := by
    funext x
    rw [residueRowSystem_reduction]
  rw [hE]
  exact hmap.symm

theorem primePowerLocalAlpha_base_invariance (p q d A B : ℕ) [NeZero p] (hAB : A ≤ B)
    (a : Fin q → ℕ) (ha : ∀ u, a u ≤ A) (c : Fin q → Fin d → ℤ) :
    primePowerLocalAlpha p q d B a (fun u => (ha u).trans hAB) c =
      primePowerLocalAlpha p q d A a ha c := by
  unfold primePowerLocalAlpha
  congr 1
  exact residueRowSystem_mass_reduction (p ^ B) (p ^ A) q d (pow_dvd_pow p hAB)
    (fun u => p ^ a u) (fun u => pow_dvd_pow p (ha u)) c

end Hindman168
