import Hindman168.NativeOriginalRoughProportion
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! One original rough-proportion budget for every member of a fixed finite
native family. Empty families claim no model or character existence. -/
namespace Hindman168
open Filter
open scoped Classical BigOperators
universe u

theorem native_original_rough_proportion_bound_mono {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (n d w R R' : ℕ)
    (Scale Z c C B η δ : ℝ) (L : NNReal) (hR : R ≤ R')
    (h : NativeOriginalRoughProportionBound D n d w R Scale Z c C B η δ L) :
    NativeOriginalRoughProportionBound D n d w R' Scale Z c C B η δ L := by
  intro modulus r hm hs hW hr hratio Q p hp hlog
  have hRR : (R : ℝ) ≤ R' := by exact_mod_cast hR
  exact h modulus r hm hs hW hr (hRR.trans hratio) Q p hp hlog

theorem native_finite_original_rough_proportion_uniform {s : ℕ} {ι : Type*} [Fintype ι]
    (D : ι → NativeNilmanifoldData.{u} s) (n d : ℕ) (c C B η : ℝ) (L : NNReal)
    (hc : 0 < c) (hB : 0 ≤ B) (hη : 0 < η)
    (Scale Z : ℕ → ℝ) (hScale : Tendsto Scale atTop atTop)
    (hg : ∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ w in atTop, ∀ i : ι,
      NativeOriginalRoughProportionBound (D i) n d w R (Scale w) (Z w) c C B η δ L := by
  have hEach (i : ι) := native_original_rough_proportion_uniform (D i) n d c C B η L
    hc hB hη Scale Z hScale hg hδ
  choose Ri _hRi hbound using hEach
  let R := 1+∑ i : ι, Ri i
  have hR : 0 < R := by dsimp only [R]; omega
  have hRi (i : ι) : Ri i ≤ R :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (by dsimp only [R]; omega)
  have hAll := Filter.eventually_all.mpr hbound
  refine ⟨R,hR,hAll.mono ?_⟩
  intro w hw i
  exact native_original_rough_proportion_bound_mono (D i) n d w (Ri i) R
    (Scale w) (Z w) c C B η δ L (hRi i) (hw i)

end Hindman168
