import Hindman168.RoughRescaledPieceSelection
import Hindman168.RoughRescaledDependentPieceTest
import Hindman168.UniformFiniteExpectationCongruence

namespace Hindman168
open FiniteMass
open scoped Classical

theorem rough_dependent_rescaled_selection {ι : Type*} [Fintype ι]
    (A B a : ι → ℤ) (N K t : ℕ) (hN : 0 < N) (hK : 0 < K)
    (ht : 0 < t) (hcop : t.Coprime K)
    (c Z : ℝ) (hc : 0 < c) (hZ : 0 < Z) (htZ : 2*(t : ℝ) ≤ c*Z)
    (hlen : ∀ j, c*Z ≤ (B j : ℝ)-A j)
    (X : ((ι → Fin N) × (ι → Fin K)) → Type*)
    (g : ∀ p, X p → ℝ) (Q : ∀ p, (ι → ℤ) → X p)
    (f : (ι → ℤ) → ℝ) (θ M η ε : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p v, |g p v| ≤ M)
    (herr : ∀ x ∈ Fintype.piFinset (fun j => Finset.Ico (A j) (B j)),
      |f x-g (roughBoxLabel A B N K hN hK x) (Q (roughBoxLabel A B N K hN hK x) x)| ≤ ε)
    (hgap : θ + M * (((N ^ Fintype.card ι * K ^ Fintype.card ι : ℕ) : ℝ) *
        Fintype.card ι * (5*(t : ℝ)/(c*Z))) + 2*ε < η)
    (hbad : η ≤ |expectation (uniformFinsetMass (alignmentBoxClass A B a t)) f -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (A j) (B j)))) f|) :
    ∃ (p : (ι → Fin N) × (ι → Fin K)) (v : ι → ℤ),
      let u : ι → ℤ := fun j => (p.2 j).val
      let l := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
      let r := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
      0 < (alignmentBoxClass l r v t).card ∧
      0 < (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))).card ∧
      θ < |expectation (uniformFinsetMass (alignmentBoxClass l r v t))
          (fun y => g p (Q p (roughResidueBoxAffine u K y))) -
        expectation (uniformFinsetMass (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))))
          (fun y => g p (Q p (roughResidueBoxAffine u K y)))| := by
  let approx (x : ι → ℤ) := g (roughBoxLabel A B N K hN hK x)
    (Q (roughBoxLabel A B N K hN hK x) x)
  obtain ⟨p, v, hp, htfull, hb⟩ := rough_frozen_rescaled_piece_selection A B a N K t hN hK ht hcop
    c Z hc hZ htZ hlen f approx approx θ M η ε 0 hM
    (fun x _ => hbound _ _) herr (fun x _ => by simp only [sub_self, abs_zero, le_refl])
    (by simpa only [add_zero] using hgap) hbad
  have hab : ∀ j, A j ≤ B j := by
    intro j
    have hh : (0 : ℝ) < (B j : ℝ)-A j := (mul_pos hc hZ).trans_le (hlen j)
    exact_mod_cast (show (A j : ℝ) ≤ B j by linarith)
  let u : ι → ℤ := fun j => (p.2 j).val
  let l := roughResidueBoxEndpoint (roughBoxLower A B N p.1) u K
  let r := roughResidueBoxEndpoint (roughBoxUpper A B N p.1) u K
  have he : ∀ y ∈ Fintype.piFinset (fun j => Finset.Ico (l j) (r j)),
      approx (roughResidueBoxAffine u K y) = g p (Q p (roughResidueBoxAffine u K y)) := by
    intro y hy
    exact rough_rescaled_dependent_piece_test A B N K hN hK hab p X g Q y hy
  have hsub : alignmentBoxClass l r v t ⊆ Fintype.piFinset (fun j => Finset.Ico (l j) (r j)) := by
    intro y hy
    exact Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hy j)).1)
  have he1 := uniformFinsetMass_expectation_congr (alignmentBoxClass l r v t)
    (fun y => approx (roughResidueBoxAffine u K y))
    (fun y => g p (Q p (roughResidueBoxAffine u K y))) (fun y hy => he y (hsub hy))
  have he2 := uniformFinsetMass_expectation_congr (Fintype.piFinset (fun j => Finset.Ico (l j) (r j)))
    (fun y => approx (roughResidueBoxAffine u K y))
    (fun y => g p (Q p (roughResidueBoxAffine u K y))) he
  rw [he1, he2] at hb
  exact ⟨p, v, hp, htfull, hb⟩

end Hindman168
