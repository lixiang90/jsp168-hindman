import Hindman168.ReplicaCubeRows
import Hindman168.RoughPrimeEvents
import Hindman168.UnitResidueRepresentatives

/-!
# The fixed polynomial tests for replica cube moduli

Each replica modulus is a smooth integer times the rough part of an
actual polynomial value. Away from that polynomial's zero test modulo
a rough prime, the modulus is nonzero. This supplies every primitive
and pairwise independent row condition of the concrete cube system.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def predictionCubeModulus {n : ℕ} (w s : ℕ)
    (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ) : ℤ :=
  (s : ℤ) * (roughPartNat w (MvPolynomial.eval (fun j => (x j : ℤ)) f).natAbs : ℤ)

theorem roughPartNat_mod_nonzero {w p : ℕ} (hp : p.Prime) (z : ℤ)
    (hz : (z : ZMod p) ≠ 0) : (roughPartNat w z.natAbs : ZMod p) ≠ 0 := by
  have hzn : z ≠ 0 := by intro h; exact hz (by simp only [h, Int.cast_zero])
  intro hzero
  have hd : p ∣ roughPartNat w z.natAbs := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hdz := ((prime_dvd_roughPartNat (Int.natAbs_ne_zero.mpr hzn) hp).mp hd).2
  exact hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z p).mpr (Int.natCast_dvd.mpr hdz))

theorem predictionCubeModulus_mod_nonzero {n w s p : ℕ} (hp : p.Prime)
    (hs : s.Coprime p) (f : MvPolynomial (Fin n) ℤ) (x : Fin n → ℕ)
    (hf : MvPolynomial.eval (fun j => (x j : ZMod p))
      (MvPolynomial.map (Int.castRingHom (ZMod p)) f) ≠ 0) :
    (predictionCubeModulus w s f x : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz : (MvPolynomial.eval (fun j => (x j : ℤ)) f : ZMod p) ≠ 0 := by
    simpa only [integerPolynomial_natCast_eval] using hf
  have hrough := roughPartNat_mod_nonzero (w := w) hp _ hz
  have hs0 : (s : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime s p).mpr hs).ne_zero
  simpa only [predictionCubeModulus, Int.cast_mul, Int.cast_natCast] using mul_ne_zero hs0 hrough

theorem polynomial_nonzero_of_not_squarefree_bad {n : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (T : Finset (MvPolynomial (Fin n) ℤ))
    (x : Fin n → ℕ) (p : S) (hbad : ¬ squarefreeCRTBadEvent S hS T
      (fun j => (x j : ZMod (squarefreeCRTModulus S))) p)
    (f : MvPolynomial (Fin n) ℤ) (hf : f ∈ T) :
    MvPolynomial.eval (fun j => (x j : ZMod (p : ℕ)))
      (MvPolynomial.map (Int.castRingHom (ZMod (p : ℕ))) f) ≠ 0 := by
  rw [squarefreeCRTBadEvent_natCast] at hbad
  exact fun hz => hbad ⟨f, hf, hz⟩

theorem replicaCube_polynomial_pair_independent {n b d w : ℕ} (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime)
    (T : Finset (MvPolynomial (Fin n) ℤ)) (f : Fin b → MvPolynomial (Fin n) ℤ)
    (hf : ∀ q, f q ∈ T) (s : Fin b → ℕ) (x : Fin n → ℕ) (p : S)
    (hs : ∀ q, (s q).Coprime (p : ℕ)) (hbad : ¬ squarefreeCRTBadEvent S hS T
      (fun j => (x j : ZMod (squarefreeCRTModulus S))) p)
    (r t : ReplicaCubeRow b d) (hrt : r ≠ t) :
    LinearIndependent (ZMod (p : ℕ))
      ![(fun j => (replicaCubeFinCoefficient (fun q => predictionCubeModulus w (s q) (f q) x) r j : ZMod (p : ℕ))),
        (fun j => (replicaCubeFinCoefficient (fun q => predictionCubeModulus w (s q) (f q) x) t j : ZMod (p : ℕ)))] := by
  apply replicaCubeFinCoefficient_pair_independent (hS p p.property) _ _ r t hrt
  intro q
  exact predictionCubeModulus_mod_nonzero (hS p p.property) (hs q)
    (f q) x (polynomial_nonzero_of_not_squarefree_bad S hS T x p hbad (f q) (hf q))

end Hindman168
