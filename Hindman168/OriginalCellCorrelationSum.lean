import Hindman168.HarmonicGoodCellCorrelation
import Hindman168.CompleteResidueCellPartition
import Hindman168.FiniteProductExpectations

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

/-- A test zero outside a chosen finite set can be summed there, even
when the original mass has support elsewhere. -/
theorem finiteMass_expectation_eq_sum_of_zero_off {A : Type*} [DecidableEq A]
    (μ : Mass A) (S : Finset A) (f : A → ℝ) (hf : ∀ a, a ∉ S → f a = 0) :
    expectation μ f = ∑ a ∈ S, μ a * f a := by
  unfold expectation Finsupp.sum
  have hl : (∑ a ∈ μ.support ∩ S, μ a * f a) = ∑ a ∈ μ.support, μ a * f a := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro a ha hn
    have hs : a ∉ S := fun hs => hn (Finset.mem_inter.mpr ⟨ha, hs⟩)
    rw [hf a hs, mul_zero]
  rw [← hl]
  apply Finset.sum_subset Finset.inter_subset_right
  intro a ha hn
  have hs : a ∉ μ.support := fun hs => hn (Finset.mem_inter.mpr ⟨hs, ha⟩)
  rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

theorem complete_cells_integerMass_expectation_sum (X W M q : ℕ) (hM : 0 < M) (hq : 0 < q)
    (C : Finset (ℤ × Fin M)) (f V : ℤ → ℝ)
    (hzero : ∀ y, y ∉ C.biUnion (fun c =>
      intervalResidueSet (c.1 * (M * q : ℕ)) (M * q) M c.2.val) → V y = 0) :
    expectation (integerMass X W) (fun y => f y * V y) =
      ∑ c ∈ C, ∑ y ∈ intervalResidueSet (c.1 * (M * q : ℕ)) (M * q) M c.2.val,
        integerMass X W y * (f y * V y) := by
  rw [finiteMass_expectation_eq_sum_of_zero_off _ _ _ (fun y hy => by rw [hzero y hy, mul_zero])]
  exact intervalResidueSet_union_sum (M * q) M (Nat.mul_pos hM hq) C
    (fun y => integerMass X W y * (f y * V y))

/-- Integrate good-cell correlations against the original integer mass.
The probability loss is the actual total mass of complete cells, not a
silently renormalized probability or an assumed full partition. -/
theorem complete_cells_original_harmonic_correlation_lower
    (X W M q : ℕ) [NeZero q] (hX : 0 < X) (hM : 0 < M) (hWM : W ∣ M)
    (C : Finset (ℤ × Fin M)) (hC : C.Nonempty)
    (hr : ∀ c ∈ C, c.2.val.Coprime W) (hZ : 0 < harmonicNormalizer X W)
    (hlo : ∀ c ∈ C, (X : ℤ) ≤ c.1 * (M * q : ℕ))
    (hhi : ∀ c ∈ C, c.1 * (M * q : ℕ) + (M * q : ℕ) ≤ (X ^ 2 : ℕ))
    (f : ℤ → ℝ) (hf : ∀ y, |f y| ≤ 1) (V : ℤ → ℝ) (hV : ∀ y, |V y| ≤ 1)
    (d : ℕ) (hd : 0 < d) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) :
    let cell := fun c : C => intervalResidueSet (c.val.1 * (M * q : ℕ)) (M * q) M c.val.2.val
    let mass := fun c : C => ∑ y ∈ cell c, integerMass X W y
    let p := fun c : C => mass c / ∑ a, mass a
    let h := fun (c : C) (z : ZMod q) =>
      f (c.val.1 * (M * q : ℕ) + c.val.2.val + (M : ℤ) * z.val)
    δ ≤ weightedSubgroupGowersValue (⊤ : AddSubgroup (ZMod q)) p d h →
    (∀ c : C, δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c) →
      γ ≤ finiteHaarMean (fun t : Fin q =>
        f (completeResidueCellPoint c.val.1 M q c.val.2 t) *
          V (completeResidueCellPoint c.val.1 M q c.val.2 t))) →
    (∀ c : C, ¬ δ / 2 ≤ subgroupGowersValue (⊤ : AddSubgroup (ZMod q)) d (h c) →
      ∀ t : Fin q, V (completeResidueCellPoint c.val.1 M q c.val.2 t) = 0) →
    (∀ y, y ∉ C.biUnion (fun c =>
      intervalResidueSet (c.1 * (M * q : ℕ)) (M * q) M c.2.val) → V y = 0) →
    (∑ c, mass c) * (δ ^ (2 ^ d) / 2 * γ - ((M * q : ℕ) / (X : ℝ))) ≤
      expectation (integerMass X W) (fun y => f y * V y) := by
  intro cell mass p h hglobal hgood hbad hzero
  obtain ⟨c₀, hc₀⟩ := hC
  letI : Nonempty C := ⟨⟨c₀, hc₀⟩⟩
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hm (c : C) : 0 < mass c := by
    have ha : (X : ℝ) ≤ (c.val.1 : ℝ) * (M * q : ℕ) := by exact_mod_cast hlo c.val c.property
    exact completeResidueCell_integerMass_pos X W c.val.1 M q hM hq hWM c.val.2
      (hr c.val c.property) hZ (hlo c.val c.property) (hhi c.val c.property) (hx.trans_le ha)
  have ht : 0 < ∑ c, mass c := Finset.sum_pos (fun c _ => hm c) Finset.univ_nonempty
  have he := complete_cells_good_gowers_harmonic_correlation X W M q hX hM hWM
    (fun c : C => c.val.1) (fun c : C => c.val.2) (fun c => hr c.val c.property)
    hZ (fun c => hlo c.val c.property) (fun c => hhi c.val c.property)
    f hf d hd δ γ hδ hγ (fun _ => V) (fun _ => hV) hglobal hgood hbad
  have hs : expectation (integerMass X W) (fun y => f y * V y) =
      ∑ c : C, ∑ y ∈ cell c, integerMass X W y * (f y * V y) := by
    rw [complete_cells_integerMass_expectation_sum X W M q hM hq C f V hzero]
    exact (Finset.sum_coe_sort C (fun c =>
      ∑ y ∈ intervalResidueSet (c.1 * (M * q : ℕ)) (M * q) M c.2.val,
        integerMass X W y * (f y * V y))).symm
  rw [hs]
  exact (mul_comm _ _).trans_le ((le_div_iff₀ ht).mp he)

end Hindman168
