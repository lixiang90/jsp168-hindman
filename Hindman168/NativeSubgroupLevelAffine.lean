import Hindman168.NativeRationalSubgroupFiltration
import Hindman168.NativeLieRationalPairIdealBCH

/-! Genuine BCH and conjugation errors modulo the next subgroup layer.
The layers need be ideals only inside H_0, not in the ambient group. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_pair_log_error {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (n : ℕ)
    {v w : D.E} (hv : v ∈ F.layer 0) (hw : w ∈ F.layer 0)
    (hB : nativeLieAdjointDifferential (I := D.I) (G := D.G) v w ∈ F.layer n) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w) - (v+w) ∈ F.layer n := by
  exact nativeLieGlobalLogarithm_product_pair_ideal (E := D.E) (I := D.I) (G := D.G)
    ((F.layer 0).restrictScalars ℚ) ((F.layer n).restrictScalars ℚ)
    (F.antitone (Nat.zero_le n))
    (fun a ha b hb => by
      change nativeLieAdjointDifferential (I := D.I) (G := D.G) a b ∈ F.layer n
      simpa only [Nat.zero_add] using F.bracket 0 n a b ha hb) hv hw hB

theorem native_subgroup_level_log_error {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (j : ℕ)
    {v w : D.E} (hv : v ∈ F.layer 0) (hw : w ∈ F.layer j) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w) - (v+w) ∈ F.layer (j+1) := by
  apply native_subgroup_pair_log_error D F (j+1) hv (F.antitone (Nat.zero_le j) hw)
  have hv1 : v ∈ F.layer 1 := F.initial ▸ hv
  simpa only [Nat.add_comm] using F.bracket 1 j v w hv1 hw

theorem native_subgroup_level_character_product {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (j : ℕ)
    (phi : D.E →ₗ[ℝ] ℝ) (hNext : F.layer (j+1) ≤ phi.ker)
    {v w : D.E} (hv : v ∈ F.layer 0) (hw : w ∈ F.layer j) :
    phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) w)) = phi v + phi w := by
  have he := hNext (native_subgroup_level_log_error D F j hv hw)
  change phi (_ - (v+w)) = 0 at he
  rw [map_sub, map_add] at he
  exact sub_eq_zero.mp he

theorem native_subgroup_level_conjugate_log_error {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (j : ℕ)
    {a v : D.E} (ha : a ∈ F.layer 0) (hv : v ∈ F.layer j) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (-a) *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v *
        nativeLieExponential (E := D.E) (I := D.I) (G := D.G) a) - v ∈ F.layer (j+1) := by
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let log : D.G → D.E := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
  let z := log (exp (-a) * exp v)
  let e := z - (-a+v)
  have he : e ∈ F.layer (j+1) :=
    native_subgroup_level_log_error D F j ((F.layer 0).neg_mem ha) hv
  have hz : z ∈ F.layer 0 := by
    apply (native_rational_subgroup_layer_logarithm_iff D F 0 _).mp
    exact (nativeRationalSubgroupLayer D F 0).mul_mem
      (native_rational_subgroup_layer_exp_mem D F 0 ((F.layer 0).neg_mem ha))
      (native_rational_subgroup_layer_exp_mem D F 0 (F.antitone (Nat.zero_le j) hv))
  have hze : z = -a+v+e := by dsimp only [e]; abel
  have hB : nativeLieAdjointDifferential (I := D.I) (G := D.G) z a ∈ F.layer (j+1) := by
    rw [hze]
    simp only [map_add, _root_.add_apply, map_neg, _root_.neg_apply,
      nativeLieAdjointDifferential_self, neg_zero, zero_add]
    apply (F.layer (j+1)).add_mem
    · rw [nativeLieAdjointDifferential_skew]
      apply (F.layer (j+1)).neg_mem
      have ha1 : a ∈ F.layer 1 := F.initial ▸ ha
      simpa only [Nat.add_comm] using F.bracket 1 j a v ha1 hv
    · rw [nativeLieAdjointDifferential_skew]
      apply (F.layer (j+1)).neg_mem
      simpa only [Nat.zero_add] using F.bracket 0 (j+1) a e ha he
  have ht := native_subgroup_pair_log_error D F (j+1) hz ha hB
  have hexp : exp z = exp (-a) * exp v :=
    nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) _
  change log (exp z * exp a) - (z+a) ∈ F.layer (j+1) at ht
  rw [hexp] at ht
  have hs := (F.layer (j+1)).add_mem ht he
  convert hs using 1
  dsimp only [e]
  abel

theorem native_subgroup_level_character_mul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (j : ℕ)
    (phi : D.E →ₗ[ℝ] ℝ) (hNext : F.layer (j+1) ≤ phi.ker)
    {g h : D.G}
    (hg : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F.layer 0)
    (hh : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) h ∈ F.layer j) :
    phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (g*h)) =
      phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) +
      phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) h) := by
  have he := native_subgroup_level_character_product D F j phi hNext hg hh
  simpa only [nativeLieExponential_globalLogarithm] using he

theorem native_subgroup_level_conjugate_character {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (j : ℕ)
    (phi : D.E →ₗ[ℝ] ℝ) (hNext : F.layer (j+1) ≤ phi.ker)
    {g : D.G} (hg : nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g ∈ F.layer 0)
    {v : D.E} (hv : v ∈ F.layer j) :
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (g⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v * g) ∈ F.layer j ∧
    phi (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (g⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v * g)) = phi v := by
  have he := native_subgroup_level_conjugate_log_error D F j hg hv
  let exp : D.E → D.G := nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
  let log : D.G → D.E := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
  have hpos : exp (log g) = g := nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) g
  have hneg : exp (-log g) = g⁻¹ :=
    (nativeLieExponential_neg (E := D.E) (I := D.I) (G := D.G) (log g)).trans (congrArg Inv.inv hpos)
  have heq := congrArg₂ (fun a b : D.G => log (a * exp v * b) - v) hneg hpos
  have he' : log (g⁻¹ * exp v * g) - v ∈ F.layer (j+1) := heq ▸ he
  let z := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (g⁻¹ * nativeLieExponential (E := D.E) (I := D.I) (G := D.G) v * g)
  have hz : z = (z-v)+v := by abel
  refine ⟨?_, ?_⟩
  · change z ∈ F.layer j
    rw [hz]
    exact (F.layer j).add_mem (F.antitone (Nat.le_succ j) he') hv
  · have hphi := hNext he'
    change phi (_-v) = 0 at hphi
    rw [map_sub] at hphi
    exact sub_eq_zero.mp hphi

end Hindman168
