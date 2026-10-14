import Hindman168.NativeLieRationalPowerMembership
import Hindman168.NativeLieRationalIdealCosets
import Hindman168.NativeLieRationalInternalGeneration
import Hindman168.NativeLieRationalInternalBCH

/-! A genuine rational subspace of layer vectors exponentiating into
a given positive-root-closed subgroup. The next-layer exponential
membership is used to remove the actual BCH error; it will be proved
by terminating induction for the original specified subgroup. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieExponential_add_mem_of_internal_next
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) (K : Subgroup G)
    (hnext : ∀ n ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1),
      nativeLieExponential (I := I) (G := G) n ∈ K)
    {u w : E}
    (hu : u ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j)
    (hw : w ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j)
    (huK : nativeLieExponential (I := I) (G := G) u ∈ K)
    (hwK : nativeLieExponential (I := I) (G := G) w ∈ K) :
    nativeLieExponential (I := I) (G := G) (u + w) ∈ K := by
  have huV := nativeLieRationalInternalLayer_le V hbr j hu
  have hwV := nativeLieRationalInternalLayer_le V hbr j hw
  have hzV := nativeLieRationalBCH_mem V hbr huV hwV
  have herror := nativeLieGlobalLogarithm_product_internal_layer V hbr j huV hw
  have hzK : nativeLieExponential (I := I) (G := G)
      (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
        (nativeLieExponential (I := I) (G := G) u *
          nativeLieExponential (I := I) (G := G) w)) ∈ K := by
    rw [nativeLieExponential_globalLogarithm]
    exact K.mul_mem huK hwK
  exact nativeLieExponential_mem_of_ideal_difference V
    (nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1))
    (nativeLieRationalInternalLayer_le V hbr (j + 1))
    (fun _ hv _ hn => nativeLieRationalInternalLayer_ideal V hbr (j + 1) hv hn)
    K hnext hzV (V.add_mem huV hwV) herror hzK

noncomputable def nativeLieRationalRootLayerSubmodule
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) (K : Subgroup G)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K)
    (hnext : ∀ n ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1),
      nativeLieExponential (I := I) (G := G) n ∈ K) : Submodule ℚ E where
  carrier := {v | v ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ∧
    nativeLieExponential (I := I) (G := G) v ∈ K}
  zero_mem' := ⟨Submodule.zero_mem _,
    (nativeLieExponential_zero (I := I) (G := G)).symm ▸ K.one_mem⟩
  add_mem' := fun hu hw =>
    ⟨Submodule.add_mem _ hu.1 hw.1,
      nativeLieExponential_add_mem_of_internal_next V hbr j K hnext hu.1 hw.1 hu.2 hw.2⟩
  smul_mem' := fun q _ hv =>
    ⟨Submodule.smul_mem _ q hv.1,
      nativeLieExponential_rat_smul_mem_root_closed K hroot hv.2 q⟩

 theorem nativeLieRationalRootLayerSubmodule_mem_iff
    (V : Submodule ℚ E) (hbr : nativeLieRationalBracketClosed (I := I) (G := G) V)
    (j : ℕ) (K : Subgroup G)
    (hroot : ∀ (g : G) (n : ℕ), 0 < n → g ^ n ∈ K → g ∈ K)
    (hnext : ∀ n ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr (j + 1),
      nativeLieExponential (I := I) (G := G) n ∈ K) (v : E) :
    v ∈ nativeLieRationalRootLayerSubmodule V hbr j K hroot hnext ↔
      v ∈ nativeLieRationalInternalLayer (I := I) (G := G) V hbr j ∧
        nativeLieExponential (I := I) (G := G) v ∈ K := Iff.rfl

end Hindman168
