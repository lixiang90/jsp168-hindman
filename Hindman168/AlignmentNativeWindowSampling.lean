import Hindman168.AlignmentRawCanonicalPieces
import Hindman168.AlignmentNativeReferenceGrowth
import Hindman168.ResidualScaleVariation
import Hindman168.ConditionalProductFiberComparison

/-! The actual exposed posterior factor window is exactly the analytic
rough dyadic residue set. Smoothness and rough-unit hypotheses are derived
from the original master law, without a coprimality assumption on retained q. -/
namespace Hindman168
open Filter FiniteMass
open scoped Classical Topology
universe u

theorem alignment_native_binary_window_eq (modulus x : ℕ) :
    binaryDyadicResidueWindow modulus x =
      roughDyadicResidueSteps ((2 ^ Nat.log2 x : ℕ) : ℝ) modulus (x % modulus) := by
  ext t
  rw [binaryDyadicResidueWindow,mem_residueWindow,
    rough_dyadic_residue_steps_mem (by positivity)]
  simp only [Nat.ModEq,Nat.mod_mod,eq_comm]

theorem alignment_native_binary_window_law (modulus x : ℕ) :
    uniformFinsetMass (binaryDyadicResidueWindow modulus x) =
      uniformFinsetMass (roughDyadicResidueSteps ((2 ^ Nat.log2 x : ℕ) : ℝ)
        modulus (x % modulus)) :=
  congrArg uniformFinsetMass (alignment_native_binary_window_eq modulus x)

theorem alignment_native_window_arithmetic
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (w : ℕ) (hw : 1 ≤ w) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support) (j : Fin n) :
    0 < (F.modulus w : ℕ)*(primorial w)^w ∧
    (∀ prime : ℕ, prime.Prime → prime ∣ (F.modulus w : ℕ)*(primorial w)^w → prime ≤ w) ∧
    primorial w ∣ (F.modulus w : ℕ)*(primorial w)^w ∧
    (primorial w).Coprime (x j % ((F.modulus w : ℕ)*(primorial w)^w)) := by
  have hW : primorial w ∣ (primorial w)^w := by
    simpa only [pow_one] using pow_dvd_pow (primorial w) hw
  have hWL := hW.trans (dvd_mul_left (primorial w ^ w) (F.modulus w : ℕ))
  refine ⟨Nat.mul_pos (F.modulus w).pos (Nat.pow_pos (primorial_pos w)),?_,hWL,?_⟩
  · intro prime hp hdiv
    obtain ⟨e,he⟩ := hF.smooth_modulus w
    rw [he,←pow_add] at hdiv
    exact hp.dvd_primorial_iff.mp (hp.dvd_of_dvd_pow hdiv)
  · exact ((residue_coprime_iff (primorial w) ((F.modulus w : ℕ)*(primorial w)^w)
      (x j % ((F.modulus w : ℕ)*(primorial w)^w)) (x j) hWL rfl).mp
      (alignmentGlobalRawMass_support_coprime F w x hx j)).symm

theorem alignment_native_variable_scale_window_event_lt {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (m d w R : ℕ) (Zref c C K B η δ : ℝ) (L : NNReal)
    {n k : ℕ} {A : Finset ℚ} {P : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A P F)
    (hw : 1 ≤ w) (x : Fin n → ℕ)
    (hx : x ∈ (globalRawMass (F.cutoff w) (primorial w) n).support) (j : Fin n)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hbound : NativeRealResidualRoughProportionBound D m d w R
      ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) Zref c (C*K) B η δ L)
    (hratio : (R : ℝ) ≤ ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) /
      (((F.modulus w : ℕ)*(primorial w)^w : ℕ) : ℝ))
    (q : ℕ) (a : Fin m → ℤ) (hq : 0 < q)
    (Q : (Option (Fin m) → ℝ) → D.G) (pN : RoughVectorMvPolynomial (Option (Fin m)) D.E)
    (hpN : RoughVectorMvDegreeLE pN d)
    (hlogN : ∀ (z : ℝ) (y : Fin m → ℝ), roughVectorMvEval pN (Option.elim · z y) =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I)
        (roughNativeResidualSource D Q a q (Option.elim · z y)))
    (Zactual : ℕ → ℝ)
    (hZrange : ∀ t ∈ binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j),
      Zref ≤ Zactual t ∧ Zactual t ≤ K*Zref) :
    event (uniformFinsetMass (binaryDyadicResidueWindow ((F.modulus w : ℕ)*(primorial w)^w) (x j)))
      (fun t => RoughNativeRealResidualComplexLargeIndex D Q a q t t (Zactual t) c C L B η) < δ := by
  obtain ⟨hm,hs,hW,hr⟩ := alignment_native_window_arithmetic hF w hw x hx j
  apply rough_uniform_finset_count_bound_event_lt _ _ δ hδ
  rw [alignment_native_binary_window_eq]
  exact native_real_residual_bound_variable_scale D m d w R
    ((2 ^ Nat.log2 (x j) : ℕ) : ℝ) Zref c C K B η δ L hc hC hbound
    _ _ hm hs hW hr hratio q a hq Q pN hpN hlogN Zactual (by
      simpa only [←alignment_native_binary_window_eq] using hZrange)

end Hindman168
