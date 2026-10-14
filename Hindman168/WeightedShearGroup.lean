import Hindman168.WeightedShearPolynomial
import Mathlib.GroupTheory.Nilpotent

/-!
The group and coefficient-independent nilpotence bound in Lemma 7.7.
The central filtration is proved from actual polynomial displacement bounds.
-/

namespace Hindman168
open MvPolynomial
open scoped commutatorElement

variable {σ R : Type*} [CommRing R]

theorem WeightedShearSubstitution.mono {w : σ → ℕ} {k l : ℤ}
    {f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w k f) (h : l ≤ k) :
    WeightedShearSubstitution w l f := by
  intro i
  exact weightedShearDegreeLE_mono w (by omega) (hf i)

theorem weightedShearSubstitution_one (w : σ → ℕ) (k : ℤ) :
    WeightedShearSubstitution (R := R) w k
      (1 : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R).toAlgHom := by
  intro i
  change X i-X i ∈ weightedShearDegreeLE w ((w i : ℤ)-k)
  simp only [sub_self, Submodule.zero_mem]

theorem weightedShearSubstitution_mul {w : σ → ℕ} {k : ℤ} (hk : 0 ≤ k)
    {f g : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w k f.toAlgHom)
    (hg : WeightedShearSubstitution w k g.toAlgHom) :
    WeightedShearSubstitution w k (f*g).toAlgHom := by
  intro i
  have h₁ := (weightedShearSubstitution_lowers hk hf (hg i)).1
  have h₂ := (weightedShearDegreeLE w ((w i : ℤ)-k)).add_mem h₁ (hf i)
  change f (g (X i)-X i) + (f (X i)-X i) ∈ _ at h₂
  change f (g (X i))-X i ∈ _
  convert h₂ using 1
  rw [map_sub]
  abel

theorem weightedShearSubstitution_inv_of_one_le {w : σ → ℕ} {k : ℤ} (hk : 1 ≤ k)
    {f : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w k f.toAlgHom) :
    WeightedShearSubstitution w k f.symm.toAlgHom := by
  have hfinv := weightedShearSubstitution_inv (hf.mono hk)
  intro i
  have h := (weightedShearSubstitution_lowers (by norm_num) hfinv (hf i)).1
  have hn := (weightedShearDegreeLE w ((w i : ℤ)-k)).neg_mem h
  change -(f.symm (f (X i)-X i)) ∈ _ at hn
  change f.symm (X i)-X i ∈ _
  convert hn using 1
  rw [map_sub, AlgEquiv.symm_apply_apply]
  abel

/-- Polynomial automorphisms whose coordinate displacements have strictly lower weight. -/
def weightedShearGroup (w : σ → ℕ) :
    Subgroup (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) where
  carrier := {f | WeightedShearSubstitution w 1 f.toAlgHom}
  one_mem' := weightedShearSubstitution_one w 1
  mul_mem' := weightedShearSubstitution_mul (by norm_num)
  inv_mem' := fun hf => weightedShearSubstitution_inv hf

/-- The `k`th central-filtration level consists of displacements lowered by `k+1`. -/
def weightedShearCentral (w : σ → ℕ) (k : ℕ) :
    Subgroup (weightedShearGroup (R := R) w) where
  carrier := {f | WeightedShearSubstitution w ((k : ℤ)+1) f.val.toAlgHom}
  one_mem' := weightedShearSubstitution_one w _
  mul_mem' := weightedShearSubstitution_mul (by positivity)
  inv_mem' := weightedShearSubstitution_inv_of_one_le (by omega)

/-- Two substitutions with degree drops `a,b` commute modulo degree drop `a+b`. -/
theorem weightedShearSubstitution_commute_mod {w : σ → ℕ} {a b d : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    {f g : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w a f.toAlgHom)
    (hg : WeightedShearSubstitution w b g.toAlgHom)
    {p : MvPolynomial σ R} (hp : p ∈ weightedShearDegreeLE w d) :
    f (g p)-g (f p) ∈ weightedShearDegreeLE w (d-(a+b)) := by
  have hfg := (weightedShearSubstitution_lowers ha hf
    (weightedShearSubstitution_lowers hb hg hp).2).2
  have hgf := (weightedShearSubstitution_lowers hb hg
    (weightedShearSubstitution_lowers ha hf hp).2).2
  have hfg' : f (g p-p)-(g p-p) ∈ weightedShearDegreeLE w (d-(a+b)) := by
    simpa only [AlgEquiv.toAlgHom_apply, sub_sub, add_comm b a] using hfg
  have hgf' : g (f p-p)-(f p-p) ∈ weightedShearDegreeLE w (d-(a+b)) := by
    simpa only [AlgEquiv.toAlgHom_apply, sub_sub] using hgf
  have h := (weightedShearDegreeLE w (d-(a+b))).sub_mem hfg' hgf'
  convert h using 1
  simp only [map_sub]
  abel

/-- The actual commutator estimate, with no assumed nilpotent representation. -/
theorem weightedShearSubstitution_commutator {w : σ → ℕ} {a b : ℤ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    {f g : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R}
    (hf : WeightedShearSubstitution w a f.toAlgHom)
    (hg : WeightedShearSubstitution w b g.toAlgHom) :
    WeightedShearSubstitution w (a+b) (⁅f,g⁆).toAlgHom := by
  have hfi := weightedShearSubstitution_inv (hf.mono ha)
  have hgi := weightedShearSubstitution_inv (hg.mono hb)
  intro i
  have hq := (weightedShearSubstitution_lowers (by norm_num) hfi
    (weightedShearSubstitution_lowers (by norm_num) hgi
      (weightedShearDegreeLE_X (R := R) w i)).1).1
  have h := weightedShearSubstitution_commute_mod (by omega) (by omega) hf hg hq
  change f (g (f.symm (g.symm (X i)))) - g (f (f.symm (g.symm (X i)))) ∈ _ at h
  simp only [AlgEquiv.apply_symm_apply] at h
  exact h

/-- The constructed filtration is genuinely a descending central series. -/
theorem weightedShearCentral_isDescending (w : σ → ℕ) :
    Subgroup.IsDescendingCentralSeries (weightedShearCentral (R := R) w) := by
  constructor
  · apply top_unique
    intro f _
    exact f.property
  · intro f n hf g
    have h := weightedShearSubstitution_commutator (by omega) (by norm_num) hf g.property
    change WeightedShearSubstitution w (((n+1 : ℕ) : ℤ)+1)
      (⁅f.val,g.val⁆).toAlgHom
    simpa only [Nat.cast_add, Nat.cast_one] using h

/-- A shear with displacement degree below every coordinate weight is the identity. -/
theorem weightedShearCentral_eq_bot (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) : weightedShearCentral (R := R) w s = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  have h := hf i
  rw [weightedShearDegreeLE_neg w (by have := hw i; omega),
    Submodule.mem_bot, sub_eq_zero] at h
  exact h

/-- Lemma 7.7's dimension- and coefficient-independent nilpotence bound.
This holds even without a finite coordinate set. -/
theorem weightedShearGroup_lowerCentral_bot (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) :
    (⊤ : Subgroup (weightedShearGroup (R := R) w)).lowerCentralSeries s = ⊥ := by
  apply le_bot_iff.mp
  exact (Subgroup.descending_central_series_ge_lower _
    (weightedShearCentral_isDescending w) s).trans
      (weightedShearCentral_eq_bot w s hw).le

theorem weightedShearGroup_nilpotent (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) : Group.IsNilpotent (weightedShearGroup (R := R) w) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr
    ⟨s, weightedShearGroup_lowerCentral_bot w s hw⟩

theorem weightedShearGroup_nilpotencyClass_le (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) : Group.nilpotencyClass (weightedShearGroup (R := R) w) ≤ s := by
  letI := weightedShearGroup_nilpotent (R := R) w s hw
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
    (weightedShearGroup_lowerCentral_bot w s hw)

/-- Adding any commutative translation group keeps the same bound when `s ≥ 1`. -/
theorem weightedShearGroup_prod_lowerCentral_bot (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) (hs : 1 ≤ s) (A : Type*) [CommGroup A] :
    (⊤ : Subgroup (weightedShearGroup (R := R) w × A)).lowerCentralSeries s = ⊥ := by
  rw [Subgroup.top_lowerCentralSeries_prod, weightedShearGroup_lowerCentral_bot w s hw,
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr
      (CommGroup.nilpotencyClass_le_one.trans hs), Subgroup.bot_prod_bot]

end Hindman168
