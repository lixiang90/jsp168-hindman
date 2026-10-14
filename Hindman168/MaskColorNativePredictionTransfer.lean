import Hindman168.MaskUnitNativeReplacement
import Hindman168.MaskFiniteModelReplacementFamily

/-! Combine the actual rho-F dense-model replacement with the actual
F-S correlation estimates along the same ultrafilter. The finite path
uses those estimates only on its constructed admissible error families;
it does not assume a uniform stage bound for arbitrary native inputs. -/

namespace Hindman168
open Filter MaskOriginalSampling
open scoped Topology Classical

theorem mask_color_native_prediction_transfer {m N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (ρ F S : Fin (m+1) → ℕ → ℤ → ℝ)
    (hF : ∀ col w y, 0 ≤ F col w y ∧ F col w y ≤ 1)
    (hS : ∀ col w y, 0 ≤ S col w y ∧ S col w y ≤ 1)
    (ε : ℝ) (_hε : 0 < ε)
    (hquality : ∀ᶠ w in (U : Filter ℕ), maskModelReplacementQuality gap a C ρ F ε w)
    (htest : ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ,
      ∀ b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ,
      (∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap C w (H w) (b w)) →
      (∀ᶠ w in (U : Filter ℕ), H w (maskSourceNonemptySupport m t) =
        fun y => F (targetRootAnchor gap t) w y - S (targetRootAnchor gap t) w y) →
      ∀ᶠ w in (U : Filter ℕ), |maskOriginalSubsetCorrelation gap a C w (H w) (b w)| ≤ ε)
    (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
    (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hH : ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap C w (H w) (b w))
    (hρ : ∀ᶠ w in (U : Filter ℕ), ∀ V : NonemptyColumnSubset (m+1),
      2 ≤ V.val.card → H w V = ρ (V.val.max' V.property) w) :
    ∀ᶠ w in (U : Filter ℕ),
      |maskOriginalSubsetCorrelation gap a C w (H w) (b w) -
        maskOriginalSubsetCorrelation gap a C w
          (maskSubsetModelReplacement (H w) (fun col => S col w)) (b w)| ≤
      ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε := by
  let G (w : ℕ) := maskSubsetModelReplacement (H w) (fun col => F col w)
  let E (t : Fin (Fintype.card (LargeColumnSubset m))) (w : ℕ) :=
    Function.update (maskSubsetHybrid (G w) (fun col => S col w) t.val)
      (maskSourceNonemptySupport m t)
      (fun y => F (targetRootAnchor gap t) w y - S (targetRootAnchor gap t) w y)
  have hν := hU (maskSubsetTailMask_eventually_nonneg gap C hC)
  have hG : ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap C w (G w) (b w) := by
    filter_upwards [hH, hν] with w hw hn
    have h := maskSubsetHybrid_admissible gap C w (H w) (b w) hw (fun col => F col w)
      (fun col => hF col w) hn (Fintype.card (LargeColumnSubset m))
    simpa only [maskSubsetHybrid_full] using h
  have hE (t : Fin (Fintype.card (LargeColumnSubset m))) :
      ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap C w (E t w) (b w) := by
    filter_upwards [hG, hν] with w hw hn
    have hh := maskSubsetHybrid_admissible gap C w (G w) (b w) hw (fun col => S col w)
      (fun col => hS col w) hn t.val
    apply maskOriginalSubset_update_admissible gap C w _ (b w) hh
    intro y
    let col := targetRootAnchor gap t
    have he : |F col w y - S col w y| ≤ 1 := abs_sub_le_iff.mpr
      ⟨by linarith [(hF col w y).2, (hS col w y).1],
        by linarith [(hS col w y).2, (hF col w y).1]⟩
    exact he.trans (by linarith [hn (maskSourceNonemptySupport m t) y])
  have hbounds (t : Fin (Fintype.card (LargeColumnSubset m))) :=
    htest t (E t) b (hE t)
      (Eventually.of_forall (fun _ => by simp only [E, Function.update_self]))
  filter_upwards [hquality, hH, hρ, eventually_all.mpr hbounds] with w hq hw hr he
  have hfirst := hq (H w) (b w) hw hr
  have hsecond := mask_native_replacement_of_error_path gap a C w (G w) (b w)
    (fun col => F col w) (fun col => S col w)
    (fun V hv => by simp only [G, maskSubsetModelReplacement, if_pos hv]) ε he
  rw [maskSubsetModelReplacement_twice] at hsecond
  calc
    _ ≤ |maskOriginalSubsetCorrelation gap a C w (H w) (b w) -
          maskOriginalSubsetCorrelation gap a C w (G w) (b w)| +
        |maskOriginalSubsetCorrelation gap a C w (G w) (b w) -
          maskOriginalSubsetCorrelation gap a C w
            (maskSubsetModelReplacement (H w) (fun col => S col w)) (b w)| := abs_sub_le _ _ _
    _ ≤ ε + (Fintype.card (LargeColumnSubset m) : ℝ) * ε := add_le_add hfirst hsecond
    _ = _ := by ring

end Hindman168
