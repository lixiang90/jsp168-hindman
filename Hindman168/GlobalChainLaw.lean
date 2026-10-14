import Hindman168.Chain
import Hindman168.CoordinateProducts
import Hindman168.JointProductLaw

/-!
# Global harmonic coordinates and the disjoint chain product law

Each chain block consists of its tail and one pivot. Coordinate selection,
discarding unused coordinates, grouping, and multiplication are all actual
finite pushforwards. Their law is identified with `jointOriginal`, rather
than being postulated to have independent block products.
-/

namespace Hindman168

open scoped BigOperators Classical

namespace Chain

noncomputable def blockSplit {m : ℕ} (C : Chain m) (i : Fin m) :
    ((C.tail i : Type) ⊕ Unit) ≃ (C.block i : Type) := by
  let f : ((C.tail i : Type) ⊕ Unit) → (C.block i : Type) :=
    Sum.elim (fun a => ⟨a.1, Finset.mem_insert_of_mem a.2⟩)
      (fun _ => ⟨C.pivot i, Finset.mem_insert_self _ _⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h
    · have hab : a.1 = b.1 := congrArg (fun x : C.block i => x.1) h
      exact congrArg Sum.inl (Subtype.ext hab)
    · have hab : a.1 = C.pivot i := congrArg Subtype.val h
      exact False.elim (C.pivot_not_mem i (hab ▸ a.2))
    · have hab : C.pivot i = b.1 := congrArg Subtype.val h
      exact False.elim (C.pivot_not_mem i (hab.symm ▸ b.2))
    · exact congrArg Sum.inr (Subsingleton.elim a b)
  · intro b
    rcases Finset.mem_insert.mp b.2 with hb | hb
    · exact ⟨Sum.inr (), Subtype.ext hb.symm⟩
    · exact ⟨Sum.inl ⟨b.1, hb⟩, Subtype.ext rfl⟩

theorem blockSplit_inl {m : ℕ} (C : Chain m) (i : Fin m) (a : C.tail i) :
    (C.blockSplit i (Sum.inl a)).1 = a.1 := rfl

theorem blockSplit_inr {m : ℕ} (C : Chain m) (i : Fin m) (a : Unit) :
    (C.blockSplit i (Sum.inr a)).1 = C.pivot i := rfl

noncomputable def tailCutoffs {m : ℕ} (C : Chain m) (X : ℕ → ℕ) (i : Fin m) : List ℕ :=
  List.ofFn (fun j : Fin (C.tail i).card => X ((C.tail i).orderIsoOfFin rfl j))

noncomputable def cutoffs {m : ℕ} (C : Chain m) (X : ℕ → ℕ) (i : Fin m) : BlockCutoffs :=
  ⟨C.tailCutoffs X i, X (C.pivot i)⟩

/-- The exact law of the product of the raw coordinates in one chain block. -/
theorem block_coordinate_law {m : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ) (i : Fin m) :
    (FiniteMass.piMass (fun j : C.block i => rawMass (X j) W)).mapDomain
      (fun x => ∏ j, x j) = blockOriginal W (C.cutoffs X i) := by
  let μ : ((C.tail i : Type) ⊕ Unit) → FiniteMass.Mass ℕ :=
    Sum.elim (fun j => rawMass (X j) W) (fun _ => rawMass (X (C.pivot i)) W)
  have hr := congrArg (fun ν : FiniteMass.Mass (((C.tail i : Type) ⊕ Unit) → ℕ) =>
    ν.mapDomain (fun x => ∏ j, x j))
    (FiniteMass.piMass_reindex (fun j : C.block i => rawMass (X j) W) (C.blockSplit i))
  rw [← Finsupp.mapDomain_comp] at hr
  have hf : (fun j => rawMass (X (C.blockSplit i j)) W) = μ := by
    funext j
    cases j <;> rfl
  rw [hf] at hr
  have hs := congrArg (fun ν : FiniteMass.Mass ((↥(C.tail i) → ℕ) × (Unit → ℕ)) =>
    ν.mapDomain (fun p => (∏ j, p.1 j) * p.2 ())) (FiniteMass.piMass_sum μ)
  rw [← Finsupp.mapDomain_comp] at hs
  have ht := congrArg (fun ν : FiniteMass.Mass (ℕ × ℕ) =>
    ν.mapDomain (fun p => p.1 * p.2))
    (FiniteMass.tensor_map (FiniteMass.piMass (fun j : C.tail i => rawMass (X j) W))
      (FiniteMass.piMass (fun _ : Unit => rawMass (X (C.pivot i)) W))
      (fun x => ∏ j, x j) (fun x => x ()))
  rw [← Finsupp.mapDomain_comp, FiniteMass.piMass_unit,
    piMass_raw_product_equiv ((C.tail i).orderIsoOfFin rfl).toEquiv] at ht
  calc
    _ = (FiniteMass.piMass μ).mapDomain (fun x => ∏ j, x j) :=
      (Finsupp.mapDomain_congr (fun x _ =>
        Fintype.prod_equiv (C.blockSplit i).symm (fun j => x j)
          (fun j => x (C.blockSplit i j)) (fun j => by rw [Equiv.apply_symm_apply]))).trans hr
    _ = (FiniteMass.tensor (FiniteMass.piMass (fun j : C.tail i => rawMass (X j) W))
        (FiniteMass.piMass (fun _ : Unit => rawMass (X (C.pivot i)) W))).mapDomain
          (fun p => (∏ j, p.1 j) * p.2 ()) := by
      refine (Finsupp.mapDomain_congr (fun x _ => ?_)).trans hs
      rw [Fintype.prod_sum_type]
      simp
    _ = (FiniteMass.tensor (tailMass W (C.tailCutoffs X i))
        (rawMass (X (C.pivot i)) W)).mapDomain (fun p => p.1 * p.2) := ht
    _ = blockOriginal W (C.cutoffs X i) := FiniteMass.tensor_statistic _ _ _

/-- Embedding all block coordinates into the original finite raw sample. -/
def coordinateIndex {m N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) :
    (Σ i, (C.block i : Type)) → Fin N :=
  fun p => ⟨p.2.1, Finset.mem_range.mp (hN p.1 p.2.2)⟩

theorem coordinateIndex_injective {m N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) :
    Function.Injective (C.coordinateIndex hN) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hab : a.1 = b.1 := congrArg Fin.val h
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (C.blocks_disjoint hij) a.2 (hab.symm ▸ b.2)
  subst j
  exact congrArg (fun a => Sigma.mk i a) (Subtype.ext hab)

def sampleProducts {m N : ℕ} (C : Chain m)
    (hN : ∀ i, C.block i ⊆ Finset.range N) (x : Fin N → ℕ) : Fin m → ℕ :=
  fun i => ∏ j : C.block i, x (C.coordinateIndex hN ⟨i, j⟩)

end Chain

noncomputable def globalRawMass (X : ℕ → ℕ) (W N : ℕ) : FiniteMass.Mass (Fin N → ℕ) :=
  FiniteMass.piMass (fun j => rawMass (X j) W)

noncomputable def globalRawPMF (X : ℕ → ℕ) (W N : ℕ)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) : PMF (Fin N → ℕ) :=
  FiniteMass.piPMF (fun j => rawMass (X j) W)
    (fun j n => by rw [rawMass_apply]; exact harmonicWeight_nonneg (hZ j) n)
    (fun j => rawMass_total (hZ j))

theorem globalRawPMF_apply (X : ℕ → ℕ) (W N : ℕ)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) (x : Fin N → ℕ) :
    globalRawPMF X W N hZ x = ENNReal.ofReal (∏ j : Fin N, harmonicWeight (X j) W (x j)) := by
  rw [globalRawPMF, FiniteMass.piPMF_apply]
  simp only [rawMass_apply]

/-- Disjointness of the chain blocks, not an additional independence
assumption, identifies their joint coordinate-product law. -/
theorem global_chain_coordinate_mass {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) :
    (globalRawMass X W N).mapDomain (C.sampleProducts hN) =
      FiniteMass.piMass (fun i => blockOriginal W (C.cutoffs X i)) := by
  have h := FiniteMass.piMass_disjoint_statistics
    (fun j : Fin N => rawMass (X j) W) (C.coordinateIndex hN)
    (C.coordinateIndex_injective hN) (fun j => rawMass_total (hZ j))
    (fun (i : Fin m) (x : C.block i → ℕ) => ∏ j, x j)
  change (globalRawMass X W N).mapDomain (C.sampleProducts hN) =
    FiniteMass.piMass (fun i =>
      (FiniteMass.piMass (fun j : C.block i => rawMass (X j) W)).mapDomain
        (fun x => ∏ j, x j)) at h
  simpa only [C.block_coordinate_law] using h

/-- The original global harmonic sample gives the previously verified
list-valued joint block law exactly. Unused coordinates have been integrated out. -/
theorem global_chain_joint_mass {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) :
    (globalRawMass X W N).mapDomain (fun x => List.ofFn (C.sampleProducts hN x)) =
      jointOriginal W (List.ofFn (C.cutoffs X)) := by
  have h := congrArg (fun μ : FiniteMass.Mass (Fin m → ℕ) => μ.mapDomain List.ofFn)
    (global_chain_coordinate_mass C X W hN hZ)
  rw [← Finsupp.mapDomain_comp, FiniteMass.piMass_ofFn] at h
  have hm : List.ofFn (fun i => blockOriginal W (C.cutoffs X i)) =
      (List.ofFn (C.cutoffs X)).map (blockOriginal W) :=
    List.ofFn_comp' (C.cutoffs X) (blockOriginal W)
  rw [hm] at h
  exact h

theorem global_chain_joint_PMF {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) {W : ℕ}
    (hW : 0 < W) (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W)
    (hv : ∀ b ∈ List.ofFn (C.cutoffs X), ValidBlockCutoffs W b) :
    (globalRawPMF X W N hZ).map (fun x => List.ofFn (C.sampleProducts hN x)) =
      jointProductPMF W (List.ofFn (C.cutoffs X)) hW hv := by
  ext ys
  rw [globalRawPMF, FiniteMass.piPMF, FiniteMass.toPMF_map_apply,
    ← globalRawMass, global_chain_joint_mass C X W hN hZ, jointProductPMF_apply]

/-- The finite sampling error now applies to block products extracted from
the actual global raw sample, with all comparison-mass factors retained. -/
theorem global_chain_joint_error {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) {W : ℕ}
    (hW : 0 < W) (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W)
    (hv : ∀ b ∈ List.ofFn (C.cutoffs X), ValidBlockCutoffs W b)
    {E M : ℝ} (hM : 0 ≤ M)
    (he : ∀ b ∈ List.ofFn (C.cutoffs X),
      dilationError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ E)
    (hm : ∀ b ∈ List.ofFn (C.cutoffs X),
      residueError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ M - 1) :
    FiniteMass.distance
      ((globalRawMass X W N).mapDomain (fun x => List.ofFn (C.sampleProducts hN x)))
      (jointComparison W (List.ofFn (C.cutoffs X))) ≤
        E * ∑ i ∈ Finset.range m, M ^ i := by
  rw [global_chain_joint_mass C X W hN hZ]
  simpa only [List.length_ofFn] using
    joint_product_law_error (List.ofFn (C.cutoffs X)) hW hv hM he hm

theorem global_chain_joint_integer_mass {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) (W : ℕ)
    (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) :
    (globalRawMass X W N).mapDomain
      (fun x => (List.ofFn (C.sampleProducts hN x)).map (fun n : ℕ => (n : ℤ))) =
      jointIntegerOriginal W (List.ofFn (C.cutoffs X)) := by
  have h := congrArg (fun μ : FiniteMass.Mass (List ℕ) =>
    μ.mapDomain (fun xs => xs.map (fun n : ℕ => (n : ℤ))))
    (global_chain_joint_mass C X W hN hZ)
  rw [← Finsupp.mapDomain_comp] at h
  exact h

theorem global_chain_joint_integer_PMF_apply {m N : ℕ} (C : Chain m) (X : ℕ → ℕ)
    (W : ℕ) (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W) (zs : List ℤ) :
    ((globalRawPMF X W N hZ).map
      (fun x => (List.ofFn (C.sampleProducts hN x)).map (fun n : ℕ => (n : ℤ)))) zs =
      ENNReal.ofReal (jointIntegerOriginal W (List.ofFn (C.cutoffs X)) zs) := by
  rw [globalRawPMF, FiniteMass.piPMF, FiniteMass.toPMF_map_apply, ← globalRawMass,
    global_chain_joint_integer_mass C X W hN hZ]

theorem global_chain_integer_error {m N : ℕ} (C : Chain m) (X : ℕ → ℕ) {W : ℕ}
    (hW : 0 < W) (hN : ∀ i, C.block i ⊆ Finset.range N)
    (hZ : ∀ j : Fin N, 0 < harmonicNormalizer (X j) W)
    (hv : ∀ b ∈ List.ofFn (C.cutoffs X), ValidBlockCutoffs W b)
    {E M : ℝ} (hM : 0 ≤ M)
    (he : ∀ b ∈ List.ofFn (C.cutoffs X),
      dilationError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ E)
    (hm : ∀ b ∈ List.ofFn (C.cutoffs X),
      residueError b.pivotCutoff W (tailBound b.tailCutoffs) ≤ M - 1) :
    FiniteMass.distance ((globalRawMass X W N).mapDomain
      (fun x => (List.ofFn (C.sampleProducts hN x)).map (fun n : ℕ => (n : ℤ))))
      (jointIntegerComparison W (List.ofFn (C.cutoffs X))) ≤
        E * ∑ i ∈ Finset.range m, M ^ i := by
  rw [global_chain_joint_integer_mass C X W hN hZ]
  simpa only [List.length_ofFn] using
    integer_joint_product_law_error (List.ofFn (C.cutoffs X)) hW hv hM he hm

end Hindman168
