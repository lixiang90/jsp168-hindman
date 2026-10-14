import Hindman168.NativeResidueExceptionalDensity
import Hindman168.RoughDyadicResidueGeometry

/-! Original dyadic-residue exceptional proportions for actual real tests.
The density route uses genuine finite Szemeredi, not color van der Waerden.
All raw moduli/residues/source coefficients follow a uniform fixed threshold. -/
namespace Hindman168
open Filter
open scoped Classical Topology
universe u

def NativeDyadicExceptionalBound {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d w R : ℕ) (Scale Z c C B η δ : ℝ) (L : NNReal) : Prop :=
  ∀ modulus r : ℕ, 0 < modulus →
    (∀ prime : ℕ, prime.Prime → prime ∣ modulus → prime ≤ w) →
    primorial w ∣ modulus → (primorial w).Coprime r →
    (R : ℝ) ≤ Scale/(modulus : ℝ) →
    ∀ (Q : (Option (Fin n) → ℝ) → D.G)
      (p : RoughVectorMvPolynomial (Option (Fin n)) D.E),
    RoughVectorMvDegreeLE p d →
    (∀ (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval p (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q (Option.elim · z y))) →
    (((roughDyadicResidueSteps Scale modulus r).filter
      (fun t => RoughNativeBadIndex D Q t t Z c C L B η)).card : ℝ) <
      δ*((roughDyadicResidueSteps Scale modulus r).card : ℝ)

theorem native_dyadic_exceptional_density {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 1 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop,
      NativeDyadicExceptionalBound D n d w R (Scale w) (Z w) c C B η δ L := by
  obtain ⟨N₀,hN,hbound⟩ := native_residue_exceptional_density D n d c C B η L
    hc hC hB hη Scale Z hScale hg hδ
  refine ⟨N₀+2,by omega,?_⟩
  filter_upwards [hbound,hScale.eventually (eventually_ge_atTop 0)] with w hw hS
  intro modulus r hmod hsmooth hW hr hratio Q p hp hlog
  apply hw ⌈Scale w⌉ ⌈2*Scale w⌉ (Int.ceil_nonneg hS) modulus r hmod hsmooth hW hr Q p hp hlog
  · intro t ht
    have hh := (rough_dyadic_residue_steps_mem hS modulus r t).mp ht
    exact ⟨hh.1,hh.2.1⟩
  · apply rough_dyadic_residue_steps_card_lower (Scale w) hS modulus r N₀ hmod
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hratio

theorem native_rough_residue_bad_fraction_tendsto {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hC : 1 ≤ C) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    (modulus r : ℕ → ℕ)
    (hmod : ∀ᶠ w in atTop, 0 < modulus w)
    (hsmooth : ∀ᶠ w in atTop, ∀ prime : ℕ, prime.Prime → prime ∣ modulus w → prime ≤ w)
    (hW : ∀ᶠ w in atTop, primorial w ∣ modulus w)
    (hr : ∀ᶠ w in atTop, (primorial w).Coprime (r w))
    (hratio : Tendsto (fun w => Scale w/(modulus w : ℝ)) atTop atTop)
    (Q : ℕ → (Option (Fin n) → ℝ) → D.G)
    (p : ℕ → RoughVectorMvPolynomial (Option (Fin n)) D.E)
    (hp : ∀ w, RoughVectorMvDegreeLE (p w) d)
    (hlog : ∀ w (z : ℝ) (y : Fin n → ℝ), roughVectorMvEval (p w) (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (Q w (Option.elim · z y))) :
    Tendsto (fun w =>
      (((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeBadIndex D (Q w) t t (Z w) c C L B η)).card : ℝ) /
        ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with w
    apply lt_of_lt_of_le ha
    positivity
  · intro δ hδ
    obtain ⟨R,_hR,hbound⟩ := native_dyadic_exceptional_density D n d c C B η L
      hc hC hB hη Scale Z hScale hg hδ
    filter_upwards [hbound,hmod,hsmooth,hW,hr,hratio.eventually (eventually_ge_atTop (R : ℝ))]
      with w hw hm hs hWw hrw hR
    have he := hw (modulus w) (r w) hm hs hWw hrw hR (Q w) (p w) (hp w) (hlog w)
    have hcard : (0 : ℝ) < (roughDyadicResidueSteps (Scale w) (modulus w) (r w)).card := by
      have hn : (0 : ℝ) ≤ (Finset.card ((roughDyadicResidueSteps (Scale w) (modulus w) (r w)).filter
        (fun t => RoughNativeBadIndex D (Q w) t t (Z w) c C L B η)) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact (div_lt_iff₀ hcard).mpr (by simpa only [mul_comm] using he)

end Hindman168
