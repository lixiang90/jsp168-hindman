import Hindman168.PrincipalSubsetProductLaws
import Hindman168.OriginalBlockRawSampling

/-! A relabeled block samples exactly its original block-product law,
with the actual selected product scale times the rational color factor. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

theorem principalTail_before {n : ℕ} (e : Fin (2*n) ↪o ℕ)
    (T : Finset (Fin n)) (b : Fin n) (hbefore : ∀ k ∈ T, k < b) :
    T.image (energyPrincipal e) ⊆ Finset.range (energyPrincipal e b) := by
  intro j hj
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr ((energyPrincipal_strictMono e) (hbefore k hk))

noncomputable def principalBlockCoefficient {n : ℕ} (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (T : Finset (Fin n)) (b : Fin n) (a : ℚ) (w : ℕ) : ℕ :=
  ⌊(selectedSubsetScale M e w (insert b T) : ℚ) * a⌋₊

theorem principalBlockCoefficient_lift {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (T : Finset (Fin n)) (b : Fin n) (a : ℚ) (w : ℕ) :
    principalBlockCoefficient M e T b a w = masterColumnCoefficient M (fun _ : Fin 1 => a)
      (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 := by
  unfold principalBlockCoefficient masterColumnCoefficient
  simp only [selectedSubsetScale_eq_master e heM, Finset.image_insert]

theorem principalBlock_sampleProducts {n M : ℕ} (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (T : Finset (Fin n)) (b : Fin n)
    (hT : T.Nonempty) (hbefore : ∀ k ∈ T, k < b) (x : Fin M → ℕ) :
    (maskBlockChain (T.image (energyPrincipal e)) (energyPrincipal e b) (hT.image _)
      (principalTail_before e T b hbefore)).sampleProducts
        (maskBlockChain_block_range (T.image (energyPrincipal e))
          (selectedPrincipalIndex e heM b) (hT.image _) (principalTail_before e T b hbefore)) x 0 =
      principalSubsetProduct (insert b T) (fun k => x (selectedPrincipalIndex e heM k)) := by
  let B := maskBlockChain (T.image (energyPrincipal e)) (energyPrincipal e b)
    (hT.image _) (principalTail_before e T b hbefore)
  let hB := maskBlockChain_block_range (T.image (energyPrincipal e))
    (selectedPrincipalIndex e heM b) (hT.image _) (principalTail_before e T b hbefore)
  let f : ℕ → ℕ := fun j => if hj : j < M then x ⟨j, hj⟩ else 0
  change (∏ j : B.block 0, x ⟨j.val, Finset.mem_range.mp (hB 0 j.property)⟩) = _
  have hp : (∏ j : B.block 0, x ⟨j.val, Finset.mem_range.mp (hB 0 j.property)⟩) =
      ∏ j ∈ B.block 0, f j := by
    rw [← Finset.prod_coe_sort (B.block 0) f]
    apply Finset.prod_congr rfl
    intro j _
    dsimp only [f]
    rw [dif_pos (Finset.mem_range.mp (hB 0 j.property))]
  rw [hp]
  change (∏ j ∈ insert (energyPrincipal e b) (T.image (energyPrincipal e)), f j) = _
  rw [← Finset.image_insert, Finset.prod_image (energyPrincipal_strictMono e).injective.injOn]
  apply Finset.prod_congr rfl
  intro k _
  dsimp only [f, selectedPrincipalIndex]
  rw [dif_pos (show energyPrincipal e k < M from heM _)]

theorem MasterParameterConditions.principal_block_product_expectation {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (T : Finset (Fin n)) (b : Fin n)
    (hT : T.Nonempty) (hbefore : ∀ k ∈ T, k < b) :
    ∀ᶠ w in atTop, ∀ φ : ℤ → ℝ,
      expectation (selectedPrincipalRawMass e F w)
        (fun x => φ (principalSubsetProduct (insert b T) x : ℤ)) =
      expectation (originalBlockProductMass F (T.image (energyPrincipal e))
        (energyPrincipal e b) (hT.image _) (principalTail_before e T b hbefore) w) φ := by
  filter_upwards [hF.selected_principal_raw_expectation e heM,
    hF.block_raw_product_expectation (T.image (energyPrincipal e))
      (selectedPrincipalIndex e heM b) (hT.image _) (principalTail_before e T b hbefore)]
    with w hs hb
  intro φ
  rw [← hs (fun x => φ (principalSubsetProduct (insert b T) x : ℤ))]
  simpa only [selectedPrincipalIndex, principalBlock_sampleProducts e heM T b hT hbefore] using hb φ

theorem MasterParameterConditions.principal_block_product_event {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (T : Finset (Fin n)) (b : Fin n)
    (hT : T.Nonempty) (hbefore : ∀ k ∈ T, k < b) :
    ∀ᶠ w in atTop, ∀ E : ℤ → Prop,
      event (selectedPrincipalRawMass e F w)
        (fun x => E (principalSubsetProduct (insert b T) x : ℤ)) =
      event (originalBlockProductMass F (T.image (energyPrincipal e))
        (energyPrincipal e b) (hT.image _) (principalTail_before e T b hbefore) w) E := by
  filter_upwards [hF.principal_block_product_expectation e heM T b hT hbefore] with w hw
  intro E
  rw [event_eq_expectation, event_eq_expectation]
  exact hw (fun y => if E y then 1 else 0)

end Hindman168
