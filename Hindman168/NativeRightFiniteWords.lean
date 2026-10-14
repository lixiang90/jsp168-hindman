import Hindman168.NativeSignedRightGenerators

/-! Lift the original signed right word into its ACTUAL finite-generator
subgroup and project into its normal-core quotient. Literal reverse order,
original subgroup inclusion and all signed integer powers are retained. -/
namespace Hindman168
open Set Subgroup
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRightGeneratorElement {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (i : Fin as.length) :
    nativeRightGeneratorGroup D as :=
  ⟨nativeRightFactorGenerator D (as.get i),Subgroup.subset_closure (mem_range_self i)⟩

noncomputable def nativeRightIntegerWord {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℤ) :
    nativeRightGeneratorGroup D as :=
  (List.ofFn (fun i => nativeRightGeneratorElement D as i ^
    ((as.get i).integerCoefficient n * signedFallingProduct (as.get i).order b))).reverse.prod

noncomputable def nativeRightFiniteWord {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℤ) :
    NativeRightCoreQuotient D as :=
  QuotientGroup.mk' (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore (nativeRightIntegerWord D as n b)

theorem native_sequential_factors_right_list {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℝ) :
    nativeSequentialFactorsRight D n b as = (as.map (fun a => nativeSequentialFactorRight D a n b)).reverse.prod := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simpa only [nativeSequentialFactorsRight, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one] using congrArg (fun g : D.G => g*nativeSequentialFactorRight D a n b) ih

theorem native_right_integer_word_original {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℤ) :
    ((nativeRightIntegerWord D as n b : nativeRightGeneratorGroup D as) : D.G) =
      nativeSequentialFactorsRight D n (b : ℝ) as := by
  have hm := (nativeRightGeneratorGroup D as).subtype.map_list_prod
    (List.ofFn (fun i => nativeRightGeneratorElement D as i ^
      ((as.get i).integerCoefficient n * signedFallingProduct (as.get i).order b))).reverse
  have he : (fun i : Fin as.length => (nativeRightGeneratorGroup D as).subtype
      (nativeRightGeneratorElement D as i ^ ((as.get i).integerCoefficient n * signedFallingProduct (as.get i).order b))) =
      (fun i : Fin as.length => nativeSequentialFactorRight D (as.get i) n (b : ℝ)) := by
    funext i
    exact ((nativeRightGeneratorGroup D as).subtype.map_zpow _ _).trans
      (native_right_factor_signed_integer_power D (as.get i) n b).symm
  simp only [List.map_reverse, List.map_ofFn] at hm
  change (nativeRightIntegerWord D as n b : D.G) = _ at hm
  have hList := congrArg (fun f : Fin as.length → D.G => (List.ofFn f).reverse.prod) he
  have hArray : List.ofFn (fun i : Fin as.length => nativeSequentialFactorRight D (as.get i) n (b : ℝ)) =
      as.map (fun a => nativeSequentialFactorRight D a n (b : ℝ)) :=
    (List.ofFn_comp' as.get (fun a => nativeSequentialFactorRight D a n (b : ℝ))).trans
      (congrArg (List.map (fun a => nativeSequentialFactorRight D a n (b : ℝ))) (List.ofFn_get as))
  exact hm.trans (hList.trans ((congrArg (fun l : List D.G => l.reverse.prod) hArray).trans
    (native_sequential_factors_right_list D as n (b : ℝ)).symm))

theorem native_right_finite_word_array {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ) (b : ℤ) :
    nativeRightFiniteWord D as n b =
      (List.ofFn (fun i =>
        (QuotientGroup.mk' (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore)
          (nativeRightGeneratorElement D as i) ^
          ((as.get i).integerCoefficient n * signedFallingProduct (as.get i).order b))).reverse.prod := by
  have hm := (QuotientGroup.mk' (D.Γ.subgroupOf (nativeRightGeneratorGroup D as)).normalCore).map_list_prod
    (List.ofFn (fun i => nativeRightGeneratorElement D as i ^
      ((as.get i).integerCoefficient n * signedFallingProduct (as.get i).order b))).reverse
  simpa only [nativeRightFiniteWord, nativeRightIntegerWord, List.map_reverse, List.map_ofFn, Function.comp_def, map_zpow] using hm

theorem native_right_finite_word_period {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (as : List (NativeSequentialBinomialFactor D)) (n : ℕ)
    {b c : ℤ} (h : Int.ModEq (Nat.card (NativeRightCoreQuotient D as) : ℤ) b c) :
    nativeRightFiniteWord D as n b = nativeRightFiniteWord D as n c := by
  rw [native_right_finite_word_array, native_right_finite_word_array]
  apply congrArg (fun f : Fin as.length → NativeRightCoreQuotient D as => (List.ofFn f).reverse.prod)
  funext i
  exact finite_group_falling_powers_period _ (as.get i).order ((as.get i).integerCoefficient n) h

end Hindman168
