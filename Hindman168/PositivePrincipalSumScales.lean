import Hindman168.PositivePrincipalSumSelection
import Mathlib.Tactic

/-!
# Exact scaled inputs for the product-chain selector

The rational scales are made integral by the original master coefficient
conditions. Their block coefficients are products of individual integer
coefficients, so Lemma 2.5 applies to the exact inputs used in the counts.
-/

namespace Hindman168
open Filter
open scoped BigOperators Classical

noncomputable def principalIndividualCoefficient {n : ℕ} (M : ℕ)
    (e : Fin (2*n) ↪o ℕ) (b : Fin n → ℚ) (w : ℕ) (k : Fin n) : ℕ :=
  ⌊(masterScale (primorial w) w M {energyPrincipal e k} : ℚ) * b k⌋₊

theorem MasterParameterConditions.principal_individual_coefficients_eventually
    {d n M : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions M A P F)
    (e : Fin (2*n) ↪o ℕ) (heM : ∀ j, e j < M) :
    ∀ᶠ w in atTop, ∀ b : Fin n → ℚ, (∀ k, b k ∈ A) → ∀ k,
      0 < principalIndividualCoefficient M e b w k ∧
      (masterScale (primorial w) w M {energyPrincipal e k} : ℚ) * b k =
        principalIndividualCoefficient M e b w k := by
  filter_upwards [hF.coefficients] with w hw
  intro b hb k
  obtain ⟨c, hc, he, _⟩ := hw (b k) (hb k) {energyPrincipal e k}
    (by
      intro j hj
      have heq := Finset.mem_singleton.mp hj
      subst j
      exact Finset.mem_range.mpr (heM _)) (by simp)
  have hh : principalIndividualCoefficient M e b w k = c := by
    simp only [principalIndividualCoefficient, he, Nat.floor_natCast]
  exact ⟨hh ▸ hc, hh.symm ▸ he⟩

theorem principal_block_coefficient_product {n m M : ℕ}
    (C : PrincipalCoordinateChain n m) (e : Fin (2*n) ↪o ℕ)
    (b : Fin n → ℚ) (w : ℕ)
    (hb : ∀ k, (masterScale (primorial w) w M {energyPrincipal e k} : ℚ) * b k =
      principalIndividualCoefficient M e b w k) (i : Fin m) :
    C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w i =
      ∏ k ∈ C.block i, principalIndividualCoefficient M e b w k := by
  unfold PrincipalCoordinateChain.coefficient selectedSubsetScale
  have he : ((∏ k ∈ C.block i, masterScale (primorial w) w M {energyPrincipal e k} : ℕ) : ℚ) *
      (∏ k ∈ C.block i, b k) =
      ((∏ k ∈ C.block i, principalIndividualCoefficient M e b w k : ℕ) : ℚ) := by
    push_cast
    rw [← Finset.prod_mul_distrib]
    simp_rw [hb]
  rw [he, Nat.floor_natCast]

/-- Any bound witnessing the finite product-chain lemma also selects
an exact monochromatic product chain for the actual scaled count inputs. -/
theorem principal_scaled_product_chain_selection {n m r M : ℕ}
    (hselect : ∀ χ : ℕ → Fin r, ∀ x : Fin n → ℕ,
      ∃ C : PrincipalCoordinateChain n m, ∃ κ : Fin r,
        ∀ J : Finset (Fin m), J.Nonempty → χ (∏ i ∈ J, C.sampleProducts x i) = κ)
    (e : Fin (2*n) ↪o ℕ) (b : Fin n → ℚ) (w : ℕ)
    (hb : ∀ k, (masterScale (primorial w) w M {energyPrincipal e k} : ℚ) * b k =
      principalIndividualCoefficient M e b w k)
    (χ : ℕ → Fin r) (x : Fin n → ℕ) :
    ∃ C : PrincipalCoordinateChain n m, ∃ κ : Fin r,
      ∀ J : Finset (Fin m), J.Nonempty →
        χ (∏ i ∈ J, C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w i *
          C.sampleProducts x i) = κ := by
  obtain ⟨C, κ, hC⟩ := hselect χ (fun k => principalIndividualCoefficient M e b w k * x k)
  refine ⟨C, κ, ?_⟩
  intro J hJ
  have he (i : Fin m) : C.coefficient M e (fun j => ∏ k ∈ C.block j, b k) w i *
      C.sampleProducts x i = C.sampleProducts
        (fun k => principalIndividualCoefficient M e b w k * x k) i := by
    rw [principal_block_coefficient_product C e b w hb]
    exact Finset.prod_mul_distrib.symm
  simpa only [he] using hC J hJ

end Hindman168
