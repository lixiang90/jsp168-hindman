import Hindman168.ProductLaw

/-!
# Actual independent harmonic tail products

Empty tails have product one. Adding a cutoff adds an independent harmonic
sample through the PMF bind/map construction already identified in ProductLaw.
The tail support consists of positive W-units bounded by the product of
squared raw cutoffs, exactly the K_T needed for the block-product estimate.
-/

namespace Hindman168

open scoped BigOperators

def ValidCutoffs (Xs : List ℕ) (W : ℕ) : Prop :=
  ∀ X ∈ Xs, 2 ≤ X ∧ (W : ℝ) / X < Real.log X

theorem validCutoffs_head {X W : ℕ} {Xs : List ℕ} (hv : ValidCutoffs (X :: Xs) W) :
    2 ≤ X ∧ (W : ℝ) / X < Real.log X := hv X (List.mem_cons_self)

theorem validCutoffs_tail {X W : ℕ} {Xs : List ℕ} (hv : ValidCutoffs (X :: Xs) W) :
    ValidCutoffs Xs W := fun x hx => hv x (List.mem_cons_of_mem X hx)

noncomputable def tailMass (W : ℕ) : List ℕ → FiniteMass.Mass ℕ
  | [] => Finsupp.single 1 1
  | X :: Xs => productMass (tailMass W Xs) X W

def tailBound (Xs : List ℕ) : ℕ := (Xs.map (fun X => X ^ 2)).prod

theorem tailMass_nonneg {W : ℕ} (hW : 0 < W) (Xs : List ℕ) :
    ValidCutoffs Xs W → ∀ n, 0 ≤ tailMass W Xs n := by
  induction Xs with
  | nil =>
    intro _ n
    simp only [tailMass, Finsupp.single_apply]
    split_ifs <;> norm_num
  | cons X Xs ih =>
    intro hv n
    have hh := validCutoffs_head hv
    exact productMass_nonneg (ih (validCutoffs_tail hv)) (harmonicNormalizer_pos hh.1 hW hh.2) n

theorem tailMass_total {W : ℕ} (hW : 0 < W) (Xs : List ℕ) :
    ValidCutoffs Xs W → FiniteMass.total (tailMass W Xs) = 1 := by
  induction Xs with
  | nil => intro _; simp [tailMass, FiniteMass.total]
  | cons X Xs ih =>
    intro hv
    have hh := validCutoffs_head hv
    exact productMass_total (ih (validCutoffs_tail hv)) (harmonicNormalizer_pos hh.1 hW hh.2)

theorem tailMass_support {W : ℕ} (Xs : List ℕ) :
    ValidCutoffs Xs W → ∀ k ∈ (tailMass W Xs).support,
      0 < k ∧ k ≤ tailBound Xs ∧ W.Coprime k := by
  induction Xs with
  | nil =>
    intro _ k hk
    have he : k = 1 := by simpa [tailMass] using hk
    subst k
    simp [tailBound]
  | cons X Xs ih =>
    intro hv k hk
    obtain ⟨s, hs, n, hn, rfl⟩ := productMass_support hk
    obtain ⟨hspos, hsbound, hsco⟩ := ih (validCutoffs_tail hv) s hs
    have hh := validCutoffs_head hv
    have hnr := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    have hnpos : 0 < n := by omega
    have hnco := (Finset.mem_filter.mp hn).2
    refine ⟨Nat.mul_pos hspos hnpos, ?_, hsco.mul_right hnco.symm⟩
    simpa only [tailBound, List.map_cons, List.prod_cons, mul_comm] using
      Nat.mul_le_mul hsbound hnr.2.le

noncomputable def tailPMF (W : ℕ) (Xs : List ℕ) (hW : 0 < W) (hv : ValidCutoffs Xs W) : PMF ℕ :=
  FiniteMass.toPMF (tailMass W Xs) (tailMass_nonneg hW Xs hv) (tailMass_total hW Xs hv)

theorem tailPMF_nil (W : ℕ) (hW : 0 < W) (hv : ValidCutoffs [] W) :
    tailPMF W [] hW hv = PMF.pure 1 := by
  classical
  ext n
  simp only [tailPMF, FiniteMass.toPMF_apply, tailMass, Finsupp.single_apply, PMF.pure_apply]
  by_cases hn : n = 1
  · subst n; simp
  · simp [hn, Ne.symm hn]

/-- This equality certifies the recursive law is independent product sampling. -/
theorem tailPMF_cons {W X : ℕ} {Xs : List ℕ} (hW : 0 < W) (hv : ValidCutoffs (X :: Xs) W) :
    tailPMF W (X :: Xs) hW hv =
      productPMF (tailMass W Xs) (tailMass_nonneg hW Xs (validCutoffs_tail hv))
        (tailMass_total hW Xs (validCutoffs_tail hv)) X W
        (harmonicNormalizer_pos (validCutoffs_head hv).1 hW (validCutoffs_head hv).2) := by
  ext n
  rw [tailPMF, FiniteMass.toPMF_apply, productPMF_apply]
  rfl

/-- A genuine harmonic tail satisfies every support hypothesis; none is assumed. -/
theorem block_product_law_error {W X : ℕ} (Xs : List ℕ) (hW : 0 < W)
    (hv : ValidCutoffs Xs W) (hX : 2 ≤ X) (hlog : (W : ℝ) / X < Real.log X)
    (hKX : tailBound Xs ≤ X) :
    FiniteMass.distance (productMass (tailMass W Xs) X W)
      (productComparisonMass (tailMass W Xs) X W) ≤ dilationError X W (tailBound Xs) :=
  product_law_error (tailMass_nonneg hW Xs hv) (tailMass_total hW Xs hv)
    hX hW hKX (tailMass_support Xs hv) hlog

theorem block_product_comparison_mass_error {W X : ℕ} (Xs : List ℕ) (hW : 0 < W)
    (hv : ValidCutoffs Xs W) (hX : 2 ≤ X) (hlog : (W : ℝ) / X < Real.log X) :
    |FiniteMass.total (productComparisonMass (tailMass W Xs) X W) - 1| ≤
      residueError X W (tailBound Xs) :=
  product_comparison_mass_error (tailMass_nonneg hW Xs hv) (tailMass_total hW Xs hv)
    hX hW (tailMass_support Xs hv) hlog

end Hindman168
