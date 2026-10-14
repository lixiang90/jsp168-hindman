import Hindman168.NativeFiniteProductManifold

/-! The actual iterated product has exactly n+1 original coordinates;
equality at all of those coordinates determines the original product. -/

namespace Hindman168

def nativeFiniteProductCoordinate {X : Type*} :
    (n : ℕ) → nativeFiniteProduct X n → Fin (n + 1) → X
  | 0, x, _ => x
  | n + 1, x, i => Fin.lastCases x.2 (fun j => nativeFiniteProductCoordinate n x.1 j) i

theorem nativeFiniteProductCoordinate_castSucc {X : Type*} (n : ℕ)
    (x : nativeFiniteProduct X (n + 1)) (i : Fin (n + 1)) :
    nativeFiniteProductCoordinate (n + 1) x i.castSucc =
      nativeFiniteProductCoordinate n x.1 i := by
  simp [nativeFiniteProductCoordinate]

theorem nativeFiniteProductCoordinate_last {X : Type*} (n : ℕ)
    (x : nativeFiniteProduct X (n + 1)) :
    nativeFiniteProductCoordinate (n + 1) x (Fin.last (n + 1)) = x.2 := by
  simp [nativeFiniteProductCoordinate]

theorem nativeFiniteProductCoordinate_injective {X : Type*} (n : ℕ) :
    Function.Injective (nativeFiniteProductCoordinate (X := X) n) := by
  induction n with
  | zero =>
    intro x y h
    exact congrFun h 0
  | succ n ih =>
    intro x y h
    apply Prod.ext
    · apply ih
      funext i
      have hi := congrFun h i.castSucc
      simpa only [nativeFiniteProductCoordinate_castSucc] using hi
    · have hi := congrFun h (Fin.last (n + 1))
      simpa only [nativeFiniteProductCoordinate_last] using hi

end Hindman168
