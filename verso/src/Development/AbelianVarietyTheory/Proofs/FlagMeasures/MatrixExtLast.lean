import Mathlib

namespace GlobalTheory.MatrixExtLast

/- English proof (translation)
Use extensionality with `i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact h₄`.

Consider the case `cast j => exact h₃ j`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact h₂ i`. Consider the case `cast j => exact h₁ i j`.
-/
theorem matrix_ext_last {k : ℕ} {M N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (h₁ : ∀ i j : Fin k, M (Fin.castSucc i) (Fin.castSucc j) = N (Fin.castSucc i) (Fin.castSucc j))
    (h₂ : ∀ i : Fin k, M (Fin.castSucc i) (Fin.last k) = N (Fin.castSucc i) (Fin.last k))
    (h₃ : ∀ j : Fin k, M (Fin.last k) (Fin.castSucc j) = N (Fin.last k) (Fin.castSucc j))
    (h₄ : M (Fin.last k) (Fin.last k) = N (Fin.last k) (Fin.last k)) : M = N := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact h₄
    | cast j => exact h₃ j
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact h₂ i
    | cast j => exact h₁ i j

end GlobalTheory.MatrixExtLast
