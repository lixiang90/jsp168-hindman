import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport
import Hindman168.IntegerIntervalGowersZeroExtension

namespace Hindman168
open scoped BigOperators Classical
open OAI.Erdos3

noncomputable def booleanFinsetEquiv (d : ℕ) : (Fin d → Bool) ≃ Finset (Fin d) where
  toFun ω := Finset.univ.filter (fun i => ω i = true)
  invFun S i := decide (i ∈ S)
  left_inv ω := by funext i; simp
  right_inv S := by ext i; simp

theorem cubeShift_booleanFinset (d : ℕ) (h : Fin d → ℤ) (ω : Fin d → Bool) :
    cubeShift h ω = ∑ i ∈ booleanFinsetEquiv d ω, h i := by
  simp [cubeShift, booleanFinsetEquiv, Finset.sum_filter]

noncomputable def integerIntervalSupportedCubeEquiv (d L : ℕ) :
    ↥(integerIntervalCubeDomain d L) ≃ SupportedCube d (↑(Finset.Ico (0 : ℤ) L) : Set ℤ) where
  toFun p := ⟨(p.val.2, p.val.1), fun ω => by
    simpa [cubeShift_booleanFinset, integerCubeVertex] using
      (mem_integerIntervalCubeDomain p.val).mp p.property (booleanFinsetEquiv d ω)⟩
  invFun p := ⟨(p.val.2, p.val.1), (mem_integerIntervalCubeDomain _).mpr (fun S => by
    have h := p.property ((booleanFinsetEquiv d).symm S)
    simpa [cubeShift_booleanFinset, integerCubeVertex] using h)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

@[simp] theorem conjugationPower_ofReal (n : ℕ) (r : ℝ) :
    conjugationPower n (r : ℂ) = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [conjugationPower] using congrArg star ih

 theorem mixedCubeProduct_integerPeriodic (q d : ℕ) (v : ZMod q → ℝ)
    (p : ℤ × (Fin d → ℤ)) :
    mixedCubeProduct (fun _ (z : ℤ) => (v (z : ZMod q) : ℂ)) p.2 p.1 =
      (integerPeriodicCubeProduct q d v p : ℂ) := by
  simp only [mixedCubeProduct, conjugationPower_ofReal, integerPeriodicCubeProduct,
    Complex.ofReal_prod]
  apply Fintype.prod_equiv (booleanFinsetEquiv d)
  intro ω
  simp [integerCubeVertex, cubeShift_booleanFinset]

theorem supportedCubeSum_integerInterval (q d L : ℕ) (v : ZMod q → ℝ) :
    supportedCubeSum d (↑(Finset.Ico (0 : ℤ) L) : Set ℤ)
      (fun _ (z : ℤ) => (v (z : ZMod q) : ℂ)) =
    ((∑ p ∈ integerIntervalCubeDomain d L, integerPeriodicCubeProduct q d v p : ℝ) : ℂ) := by
  rw [supportedCubeSum, Complex.ofReal_sum]
  rw [← Finset.sum_coe_sort (integerIntervalCubeDomain d L)
    (fun p => (integerPeriodicCubeProduct q d v p : ℂ))]
  symm
  apply Fintype.sum_equiv (integerIntervalSupportedCubeEquiv d L)
  intro p
  exact (mixedCubeProduct_integerPeriodic q d v p.val).symm

theorem card_supportedCube_integerInterval (d L : ℕ) :
    Nat.card (SupportedCube d (↑(Finset.Ico (0 : ℤ) L) : Set ℤ)) =
      (integerIntervalCubeDomain d L).card := by
  rw [← Nat.card_congr (integerIntervalSupportedCubeEquiv d L)]
  simp

theorem finiteSupportGowersNorm_integerInterval (q d L : ℕ) (v : ZMod q → ℝ) :
    finiteSupportGowersNorm d (Finset.Ico (0 : ℤ) L)
      (fun z => (v (z : ZMod q) : ℂ)) = integerIntervalPeriodicGowersValue q d L v := by
  simp only [finiteSupportGowersNorm, supportedCubeSum_integerInterval,
    Complex.ofReal_re, card_supportedCube_integerInterval,
    integerIntervalPeriodicGowersValue, integerIntervalPeriodicCubeMean]

theorem interval_intCast_reflectsPairSums (L M : ℕ) (hM : 2 * (L - 1) < M) :
    ReflectsPairSums (Int.castAddHom (ZMod M)) (↑(Finset.Ico (0 : ℤ) L) : Set ℤ) := by
  intro a ha b hb c hc e he h
  simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb hc he
  have hab : 0 ≤ a + b ∧ a + b < M := by omega
  have hce : 0 ≤ c + e ∧ c + e < M := by omega
  have hcast : ((a + b : ℤ) : ZMod M) = ((c + e : ℤ) : ZMod M) := by
    simpa using h
  have hm := (ZMod.intCast_eq_intCast_iff' (a+b) (c+e) M).mp hcast
  simpa [Int.emod_eq_of_lt hab.1 hab.2, Int.emod_eq_of_lt hce.1 hce.2] using hm

end Hindman168
