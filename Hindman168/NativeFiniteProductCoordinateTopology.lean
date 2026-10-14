import Hindman168.NativeFiniteProductCoordinates

/-! Continuity in the recursively constructed product is detected by its
actual coordinates. This uses the inherited product topology. -/

namespace Hindman168

attribute [local instance] nativeFiniteProductTopologicalSpace

theorem nativeFiniteProductCoordinate_continuous {X : Type*} [TopologicalSpace X]
    (n : ℕ) (i : Fin (n + 1)) :
    Continuous (fun x : nativeFiniteProduct X n => nativeFiniteProductCoordinate n x i) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    letI := nativeFiniteProductTopologicalSpace (X := X) n
    refine Fin.lastCases ?_ ?_ i
    · simp only [nativeFiniteProductCoordinate_last]
      change Continuous (fun x : nativeFiniteProduct X n × X => x.2)
      exact continuous_snd
    · intro j
      simp only [nativeFiniteProductCoordinate_castSucc]
      change Continuous (fun x : nativeFiniteProduct X n × X => nativeFiniteProductCoordinate n x.1 j)
      exact (ih j).comp continuous_fst

theorem nativeFiniteProduct_continuous_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (f : Y → nativeFiniteProduct X n) :
    Continuous f ↔ ∀ i, Continuous (fun y => nativeFiniteProductCoordinate n (f y) i) := by
  constructor
  · intro h i
    exact (nativeFiniteProductCoordinate_continuous n i).comp h
  · induction n with
    | zero => intro h; exact h 0
    | succ n ih =>
      intro h
      apply Continuous.prodMk
      · apply ih (fun y => (f y).1)
        intro i
        simpa only [nativeFiniteProductCoordinate_castSucc] using h i.castSucc
      · simpa only [nativeFiniteProductCoordinate_last] using h (Fin.last (n + 1))

end Hindman168
