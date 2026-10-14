import Hindman168.AlignmentTailRestTuple

/-! Original PRODUCT support supplies actual rest windows without a posterior
key assumption. These windows fix dyadic scale and retained normalization. -/
namespace Hindman168
open FiniteMass
open scoped Classical BigOperators

theorem alignment_tail_rest_supported_window {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (modulus : ℕ) (j : T) (rest : {k : T // k ≠ j} → ℕ)
    (hr : rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
      (binaryDyadicResidueWindow modulus (x k.val.val)))).support) (k : {k : T // k ≠ j}) :
    rest k ∈ binaryDyadicResidueWindow modulus (x k.val.val) := by
  have hn := Finsupp.mem_support_iff.mp hr
  rw [piMass_apply] at hn
  have hs := Finsupp.mem_support_iff.mpr (Finset.prod_ne_zero_iff.mp hn k (Finset.mem_univ k))
  exact flatMass_support _ _ hs

theorem alignment_tail_rest_all_windows {N : ℕ} (T : Finset (Fin N))
    (x : Fin N → ℕ) (modulus : ℕ) (j : T) (rest : {k : T // k ≠ j} → ℕ)
    (hr : rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
      (binaryDyadicResidueWindow modulus (x k.val.val)))).support)
    (t : ℕ) (ht : t ∈ binaryDyadicResidueWindow modulus (x j.val)) :
    ∀ k ∈ T, alignmentTailTuple T x (insertPivotCoordinate j rest t) k ∈
      binaryDyadicResidueWindow modulus (x k) := by
  intro k hk
  rw [alignment_tail_tuple_inside T x _ (⟨k,hk⟩ : T)]
  by_cases hkj : (⟨k,hk⟩ : T)=j
  · subst j
    rw [insertPivotCoordinate_self]
    exact ht
  · simp only [insertPivotCoordinate,dif_neg hkj]
    exact alignment_tail_rest_supported_window T x modulus j rest hr ⟨⟨k,hk⟩,hkj⟩

theorem alignment_window_value_positive {modulus x t : ℕ}
    (ht : t ∈ binaryDyadicResidueWindow modulus x) : 0 < t := by
  rw [binaryDyadicResidueWindow,mem_residueWindow] at ht
  have hp : (0 : ℝ) < (2 ^ Nat.log2 x : ℕ) := by positivity
  have htp : (0 : ℝ) < t := hp.trans_le ht.1
  exact_mod_cast htp

theorem alignment_cube_scale_window_eq {N : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin N) (T : Finset (Fin N)) (x y : Fin N → ℕ) (modulus : ℕ)
    (hwin : ∀ k ∈ T, y k ∈ binaryDyadicResidueWindow modulus (x k)) :
    alignmentCubeScale F w i T y=alignmentCubeScale F w i T x := by
  unfold alignmentCubeScale alignmentShortBinVolume
  congr 3
  apply Finset.prod_congr rfl
  intro k hk
  rw [((binaryDyadicResidueWindow_mem (alignment_window_value_positive (hwin k hk))).mp (hwin k hk)).1]

theorem alignment_tail_rest_cube_scale {N : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin N) (T : Finset (Fin N)) (x : Fin N → ℕ) (modulus : ℕ)
    (j : T) (rest : {k : T // k ≠ j} → ℕ)
    (hr : rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
      (binaryDyadicResidueWindow modulus (x k.val.val)))).support)
    (t : ℕ) (ht : t ∈ binaryDyadicResidueWindow modulus (x j.val)) :
    alignmentCubeScale F w i T (alignmentTailTuple T x (insertPivotCoordinate j rest t))=
      alignmentCubeScale F w i T x :=
  alignment_cube_scale_window_eq F w i T x _ modulus
    (alignment_tail_rest_all_windows T x modulus j rest hr t ht)

theorem alignment_tail_rest_retained_scale_range {N : ℕ} (F : MasterParameterFamily)
    (w : ℕ) (i : Fin N) (T U : Finset (Fin N)) (hU : U ⊆ T)
    (x : Fin N → ℕ) (modulus d : ℕ) (hd : 0 < d) (hx : ∀ k ∈ U, 0 < x k)
    (j : T) (rest : {k : T // k ≠ j} → ℕ)
    (hr : rest ∈ (piMass (fun k : {k : T // k ≠ j} => uniformFinsetMass
      (binaryDyadicResidueWindow modulus (x k.val.val)))).support)
    (t : ℕ) (ht : t ∈ binaryDyadicResidueWindow modulus (x j.val)) :
    let y := alignmentTailTuple T x (insertPivotCoordinate j rest t)
    let K : ℝ := 2^T.card
    alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*K) ≤
      alignmentCubeScale F w i T y/((d : ℝ)*alignmentNaturalBlockProduct y U) ∧
    alignmentCubeScale F w i T y/((d : ℝ)*alignmentNaturalBlockProduct y U) ≤
      K^2*(alignmentCubeScale F w i T x/((d : ℝ)*alignmentNaturalBlockProduct x U*K)) := by
  dsimp only
  rw [alignment_tail_rest_cube_scale F w i T x modulus j rest hr t ht]
  exact alignment_window_retained_normalized_scale x _ T U hU modulus d hd hx
    (fun k hk => alignment_tail_rest_all_windows T x modulus j rest hr t ht k (hU hk))
    (alignmentCubeScale F w i T x) (by unfold alignmentCubeScale; positivity)

end Hindman168
