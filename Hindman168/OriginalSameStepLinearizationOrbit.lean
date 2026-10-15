import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Exact integer orbits in a shift semidirect product

This file supplies the algebraic orbit calculation used in a same-step linearization.
There are no polynomiality or nilpotence assumptions here.  Those assumptions belong to
the construction of the translation-invariant subgroup in which the step lies.

For the standard semidirect-product multiplication and the forward translation action,
the correct telescoping convention is the right difference
`g(k)⁻¹ * g(k+1)`.  Its integer powers have first coordinate
`g(k)⁻¹ * g(k+n)`.  In particular the initial value is retained explicitly:
`g(0) * (step ^ n).left(0) = g(n)` for every `n : ℤ`.
-/

namespace Hindman168
namespace OriginalSameStepLinearizationOrbit

variable {G : Type*} [Group G]

/-- Translation of a group-valued integer sequence by an integer. -/
def translation (t : ℤ) : MulAut (ℤ → G) where
  toFun f k := f (k + t)
  invFun f k := f (k - t)
  left_inv f := by funext k; simp
  right_inv f := by funext k; simp
  map_mul' f h := rfl

@[simp] theorem translation_apply (t k : ℤ) (f : ℤ → G) :
    translation t f k = (f : ℤ → G) (k + t) := rfl

/-- The full integer translation action, as a homomorphism to automorphisms. -/
def translationAction : Multiplicative ℤ →* MulAut (ℤ → G) where
  toFun t := translation t.toAdd
  map_one' := by ext f k; simp [translation]
  map_mul' s t := by ext f k; simp [translation, add_assoc]

@[simp] theorem translationAction_apply (t : Multiplicative ℤ) (f : ℤ → G) (k : ℤ) :
    translationAction t f k = (f : ℤ → G) (k + t.toAdd) := rfl

/-- The ambient shift extension. -/
abbrev ShiftExtension (G : Type*) [Group G] :=
  (ℤ → G) ⋊[translationAction] Multiplicative ℤ

/-- The right difference, matching the multiplication in `ShiftExtension`. -/
def rightDifference (g : ℤ → G) : ℤ → G := fun k => (g k)⁻¹ * g (k + 1)

@[simp] theorem rightDifference_apply (g : ℤ → G) (k : ℤ) :
    rightDifference g k = (g k)⁻¹ * g (k + 1) := rfl

/-- The left difference, for callers using the opposite derivative convention. -/
def leftDifference (g : ℤ → G) : ℤ → G := fun k => g (k + 1) * (g k)⁻¹

/-- Passing to the inverse sequence converts a left difference to a right difference. -/
theorem rightDifference_inv (g : ℤ → G) :
    rightDifference (fun k => (g k)⁻¹) = (leftDifference g)⁻¹ := by
  funext k
  simp [rightDifference, leftDifference]

/-- The entire integer orbit is a genuine homomorphism into the shift extension. -/
def orbitHom (g : ℤ → G) : Multiplicative ℤ →* ShiftExtension G where
  toFun t := ⟨fun k => (g k)⁻¹ * g (k + t.toAdd), t⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext k
      simp
    · rfl
  map_mul' s t := by
    apply SemidirectProduct.ext
    · funext k
      simp [mul_assoc, add_assoc]
    · rfl

@[simp] theorem orbitHom_left (g : ℤ → G) (t : Multiplicative ℤ) (k : ℤ) :
    (orbitHom g t).left k = (g k)⁻¹ * g (k + t.toAdd) := rfl

@[simp] theorem orbitHom_right (g : ℤ → G) (t : Multiplicative ℤ) :
    (orbitHom g t).right = t := rfl

/-- A single fixed element whose integer powers realize the sequence. -/
def step (g : ℤ → G) : ShiftExtension G :=
  ⟨rightDifference g, Multiplicative.ofAdd 1⟩

theorem step_eq_orbitHom (g : ℤ → G) :
    step g = orbitHom g (Multiplicative.ofAdd 1) := rfl

/-- Exact powers for all integers, including negative integers. -/
theorem step_zpow (g : ℤ → G) (n : ℤ) :
    step g ^ n = orbitHom g (Multiplicative.ofAdd n) := by
  rw [step_eq_orbitHom, ← map_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

@[simp] theorem step_zpow_left (g : ℤ → G) (n k : ℤ) :
    (step g ^ n).left k = (g k)⁻¹ * g (k + n) := by
  rw [step_zpow]
  rfl

@[simp] theorem step_zpow_right (g : ℤ → G) (n : ℤ) :
    (step g ^ n).right = Multiplicative.ofAdd n := by
  rw [step_zpow]
  rfl

/-- The value at any anchor, with its necessary initial-value factor. -/
theorem read_zpow_at (g : ℤ → G) (n k : ℤ) :
    g k * (step g ^ n).left k = g (k + n) := by
  simp

/-- Reading the orbit based at the identity recovers the original sequence exactly. -/
theorem read_orbit (g : ℤ → G) (n : ℤ) :
    g 0 * ((step g ^ n) * (1 : ShiftExtension G)).left 0 = g n := by
  simp

/-- Any observable can be applied to the exact orbit readout. -/
theorem observable_orbit {X : Type*} (F : G → X) (g : ℤ → G) (n : ℤ) :
    F (g 0 * ((step g ^ n) * (1 : ShiftExtension G)).left 0) = F (g n) := by
  rw [read_orbit]

/-- Right normalization makes the value at zero the identity. -/
def normalize (g : ℤ → G) : ℤ → G := fun k => g k * (g 0)⁻¹

@[simp] theorem normalize_zero (g : ℤ → G) : normalize g 0 = 1 := by
  simp [normalize]

/-- The normalized right difference, including its constant conjugation. -/
theorem rightDifference_normalize (g : ℤ → G) (k : ℤ) :
    rightDifference (normalize g) k =
      g 0 * (g k)⁻¹ * g (k + 1) * (g 0)⁻¹ := by
  simp [rightDifference, normalize, mul_assoc]

/-- Constant initial-value basepoint; the observable need only evaluate at zero. -/
def basepoint (g : ℤ → G) : ShiftExtension G :=
  ⟨fun _ => g 0, 1⟩

/-- A parameter-independent evaluation observable, with the initial value in the basepoint. -/
theorem based_orbit (g : ℤ → G) (n : ℤ) :
    ((step (normalize g) ^ n) * basepoint g).left 0 = g n := by
  change (step (normalize g) ^ n).left 0 * g 0 = g n
  rw [step_zpow_left]
  simp [normalize, mul_assoc]

section AbstractAction

variable {P : Type*} [Group P]
  (φ : Multiplicative ℤ →* MulAut P) (ρ : P →* (ℤ → G))
  (hρ : ∀ (t : Multiplicative ℤ) (p : P) (k : ℤ),
    ρ (φ t p) k = ρ p (k + t.toAdd))

/-- An equivariant sequence representation induces a map of shift extensions. -/
def realizationMap : (P ⋊[φ] Multiplicative ℤ) →* ShiftExtension G :=
  SemidirectProduct.map ρ (MonoidHom.id _) (by
    intro t
    ext p k
    exact hρ t p k)

@[simp] theorem realizationMap_left (x : P ⋊[φ] Multiplicative ℤ) :
    (realizationMap φ ρ hρ x).left = ρ x.left := rfl

@[simp] theorem realizationMap_right (x : P ⋊[φ] Multiplicative ℤ) :
    (realizationMap φ ρ hρ x).right = x.right := rfl

include hρ

/-- Abstract-action version: lifting the single right difference is sufficient.
No assumption about lifting the whole sequence `g` is made. -/
theorem abstract_step_zpow_left (g : ℤ → G) (d : P)
    (hd : ρ d = rightDifference g) (n k : ℤ) :
    ρ ((⟨d, Multiplicative.ofAdd 1⟩ : P ⋊[φ] Multiplicative ℤ) ^ n).left k =
      (g k)⁻¹ * g (k + n) := by
  have hstep : realizationMap φ ρ hρ
      (⟨d, Multiplicative.ofAdd 1⟩ : P ⋊[φ] Multiplicative ℤ) = step g := by
    apply SemidirectProduct.ext
    · exact hd
    · rfl
  have hpow := congrArg (fun x : ShiftExtension G => x.left k)
    (map_zpow (realizationMap φ ρ hρ)
      (⟨d, Multiplicative.ofAdd 1⟩ : P ⋊[φ] Multiplicative ℤ) n)
  rw [hstep, step_zpow_left] at hpow
  exact hpow

/-- Exact orbit readout for any abstract group with an equivariant sequence map. -/
theorem abstract_read_orbit (g : ℤ → G) (d : P)
    (hd : ρ d = rightDifference g) (n : ℤ) :
    g 0 * ρ (((⟨d, Multiplicative.ofAdd 1⟩ : P ⋊[φ] Multiplicative ℤ) ^ n) * 1).left 0 =
      g n := by
  rw [mul_one, abstract_step_zpow_left φ ρ hρ g d hd]
  simp

/-- General representation version with the initial value in an actual basepoint.
The readout is plain evaluation; it does not multiply by a sequence-dependent factor. -/
theorem abstract_based_orbit (g : ℤ → G) (d c : P)
    (hd : ρ d = rightDifference (normalize g))
    (hc : ρ c = fun _ => g 0) (n : ℤ) :
    ρ ((((⟨d, Multiplicative.ofAdd 1⟩ : P ⋊[φ] Multiplicative ℤ) ^ n) *
      (⟨c, 1⟩ : P ⋊[φ] Multiplicative ℤ)).left) 0 = g n := by
  simp only [SemidirectProduct.mul_left, map_mul, Pi.mul_apply]
  rw [hρ, hc, abstract_step_zpow_left φ ρ hρ (normalize g) d hd]
  simp [normalize, mul_assoc]

end AbstractAction

section TranslationInvariantSubgroup

variable (P : Subgroup (ℤ → G))
  (hP : ∀ (t : ℤ) (f : ℤ → G), f ∈ P → translation t f ∈ P)

/-- Restriction of translation to a translation-invariant subgroup. -/
def subgroupTranslation (t : ℤ) : MulAut P where
  toFun f := ⟨translation t f, hP t f f.property⟩
  invFun f := ⟨translation (-t) f, hP (-t) f f.property⟩
  left_inv f := by apply Subtype.ext; funext k; simp
  right_inv f := by apply Subtype.ext; funext k; simp
  map_mul' f h := rfl

@[simp] theorem subgroupTranslation_apply (t k : ℤ) (f : P) :
    (subgroupTranslation P hP t f : ℤ → G) k = (f : ℤ → G) (k + t) := rfl

/-- The restricted integer translation action. -/
def subgroupTranslationAction : Multiplicative ℤ →* MulAut P where
  toFun t := subgroupTranslation P hP t.toAdd
  map_one' := by ext f k; simp
  map_mul' s t := by ext f k; simp [add_assoc]

@[simp] theorem subgroupTranslationAction_apply
    (t : Multiplicative ℤ) (f : P) (k : ℤ) :
    (subgroupTranslationAction P hP t f : ℤ → G) k = (f : ℤ → G) (k + t.toAdd) := rfl

/-- The shift extension of a translation-invariant subgroup. -/
abbrev SubgroupShiftExtension := P ⋊[subgroupTranslationAction P hP] Multiplicative ℤ

/-- The step lies in the subgroup extension as soon as its right difference lies in `P`. -/
def subgroupStep (g : ℤ → G) (hd : rightDifference g ∈ P) :
    SubgroupShiftExtension P hP :=
  ⟨⟨rightDifference g, hd⟩, Multiplicative.ofAdd 1⟩

/-- All integer powers telescope inside the smaller subgroup extension. -/
theorem subgroupStep_zpow_left (g : ℤ → G) (hd : rightDifference g ∈ P) (n k : ℤ) :
    (((subgroupStep P hP g hd ^ n).left : P) : ℤ → G) k =
      (g k)⁻¹ * g (k + n) := by
  exact abstract_step_zpow_left (subgroupTranslationAction P hP) P.subtype
    (fun _ _ _ => rfl) g ⟨rightDifference g, hd⟩ rfl n k

/-- Exact sequence recovery in the subgroup extension, with identity basepoint. -/
theorem subgroup_read_orbit (g : ℤ → G) (hd : rightDifference g ∈ P) (n : ℤ) :
    g 0 * ((((subgroupStep P hP g hd ^ n) *
      (1 : SubgroupShiftExtension P hP)).left : P) : ℤ → G) 0 = g n := by
  rw [mul_one, subgroupStep_zpow_left]
  simp

/-- The recovered sequence can be passed to an arbitrary observable. -/
theorem subgroup_observable_orbit {X : Type*} (F : G → X)
    (g : ℤ → G) (hd : rightDifference g ∈ P) (n : ℤ) :
    F (g 0 * ((((subgroupStep P hP g hd ^ n) *
      (1 : SubgroupShiftExtension P hP)).left : P) : ℤ → G) 0) = F (g n) := by
  rw [subgroup_read_orbit]

/-- The constant initial-value basepoint in the smaller shift extension. -/
def subgroupBasepoint (g : ℤ → G) (hc : (fun _ : ℤ => g 0) ∈ P) :
    SubgroupShiftExtension P hP :=
  ⟨⟨fun _ => g 0, hc⟩, 1⟩

/-- The initial value can be placed in the basepoint, leaving evaluation independent of `g`. -/
theorem subgroup_based_orbit (g : ℤ → G)
    (hd : rightDifference (normalize g) ∈ P) (hc : (fun _ : ℤ => g 0) ∈ P) (n : ℤ) :
    ((((subgroupStep P hP (normalize g) hd ^ n) *
      subgroupBasepoint P hP g hc).left : P) : ℤ → G) 0 = g n := by
  change (((subgroupStep P hP (normalize g) hd ^ n).left : P) : ℤ → G) 0 * g 0 = g n
  rw [subgroupStep_zpow_left]
  simp [normalize, mul_assoc]

/-- Any fixed observable is read directly from the normalized-step, nontrivial-basepoint orbit. -/
theorem subgroup_based_observable_orbit {X : Type*} (F : G → X) (g : ℤ → G)
    (hd : rightDifference (normalize g) ∈ P) (hc : (fun _ : ℤ => g 0) ∈ P) (n : ℤ) :
    F (((((subgroupStep P hP (normalize g) hd ^ n) *
      subgroupBasepoint P hP g hc).left : P) : ℤ → G) 0) = F (g n) := by
  rw [subgroup_based_orbit]

/-- A left-difference hypothesis also gives a step, by using the inverse sequence. -/
def subgroupLeftStep (g : ℤ → G) (hd : leftDifference g ∈ P) :
    SubgroupShiftExtension P hP :=
  subgroupStep P hP (fun k => (g k)⁻¹) (by
    rw [rightDifference_inv]
    exact P.inv_mem hd)

/-- The left-difference convention recovers the sequence by inverse evaluation. -/
theorem subgroup_left_read_orbit (g : ℤ → G) (hd : leftDifference g ∈ P) (n : ℤ) :
    (((((subgroupLeftStep P hP g hd ^ n) *
      (1 : SubgroupShiftExtension P hP)).left : P) : ℤ → G) 0)⁻¹ * g 0 = g n := by
  unfold subgroupLeftStep
  rw [mul_one, subgroupStep_zpow_left]
  simp [mul_assoc]

/-- An observable of the left-difference orbit, with the initial value retained. -/
theorem subgroup_left_observable_orbit {X : Type*} (F : G → X)
    (g : ℤ → G) (hd : leftDifference g ∈ P) (n : ℤ) :
    F ((((((subgroupLeftStep P hP g hd ^ n) *
      (1 : SubgroupShiftExtension P hP)).left : P) : ℤ → G) 0)⁻¹ * g 0) = F (g n) := by
  rw [subgroup_left_read_orbit]

end TranslationInvariantSubgroup

end OriginalSameStepLinearizationOrbit
end Hindman168
