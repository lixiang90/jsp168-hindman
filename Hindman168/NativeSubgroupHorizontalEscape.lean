import Hindman168.NativeSubgroupTaylorTopCoefficient

/-! All-rational-level irrationality excludes bounded actual horizontal
top coefficients. The factorial denominator is retained by using a true
nonzero rational multiple of the same geometric character. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_level_character_rat_smul {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (j : ℕ) (phi : D.E →ₗ[ℝ] ℝ) (hphi : NativeSubgroupRationalLevelCharacter D F j phi)
    (q : ℚ) (hq : q ≠ 0) : NativeSubgroupRationalLevelCharacter D F j ((q : ℝ) • phi) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨v,hv,hne⟩ := hphi.1
    exact ⟨v,hv,mul_ne_zero hqR hne⟩
  · intro v hv
    change (q : ℝ) * phi v = 0
    rw [hphi.2.1 hv, mul_zero]
  · intro a b ha hb hab v hv w hw
    change (q : ℝ) * phi _ = 0
    rw [hphi.2.2.1 a b ha hb hab v hv w hw, mul_zero]
  · intro v hv hvRat
    obtain ⟨r,hr⟩ := hphi.2.2.2 v hv hvRat
    refine ⟨q*r,?_⟩
    change (q : ℝ) * phi v = ((q*r : ℚ) : ℝ)
    rw [hr, Rat.cast_mul]

theorem native_subgroup_horizontal_top_coefficient_escape {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (phi : D.E →ₗ[ℝ] ℝ)
    (hB : ∀ v ∈ F.layer 0, ∀ w ∈ F.layer 0,
      phi (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) = 0)
    (j : ℕ) (hj : 1 ≤ j) (hjTop : j ≤ ℓ)
    (hLevel : NativeSubgroupRationalLevelCharacter D F j phi) :
    Tendsto (fun n => (L n)^j * ‖((MvPolynomial.coeff (Finsupp.single () j)
      (roughVectorMvProjection phi (p n)) : ℝ) : UnitAddCircle)‖) atTop atTop := by
  let q : ℚ := (j.factorial : ℚ)⁻¹
  have hq : q ≠ 0 := inv_ne_zero (by positivity)
  have hs := hIrr j hj hjTop ((q : ℝ) • phi)
    (native_subgroup_level_character_rat_smul D F j phi hLevel q hq)
  have he (v : D.E) : ((q : ℝ) • phi) v = phi v / (j.factorial : ℝ) := by
    change (q : ℝ) * phi v = _
    simp only [q, Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv, mul_comm]
  simpa only [native_subgroup_taylor_top_coefficient D F phi hB j hLevel.2.1 _ (hp _), he] using hs

end Hindman168
