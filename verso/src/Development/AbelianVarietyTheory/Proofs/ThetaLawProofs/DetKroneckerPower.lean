import Mathlib

namespace GlobalTheory

open Kronecker

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero`. Establish `h : (Matrix.of fun (I I' : Fin (0 + 1) → Fin N) => ∏ c, B (I c) (I' c)) = B.submatrix (Equiv.funUnique (Fin 1) (Fin N)) (Equiv.funUnique (Fin 1) (Fin N))`. Use extensionality with `I I'`. Simplify using the standard rewrite rules.

Rewrite using `[h, Matrix.det_submatrix_equiv_self]`. Simplify using the standard rewrite rules. Consider the case `succ r ih`. Establish `h : (Matrix.of fun (I I' : Fin (r + 1 + 1) → Fin N) => ∏ c, B (I c) (I' c)) = (B ⊗ₖ (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c))).submatrix (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm`. Use extensionality with `I I'`.

Rewrite using `[Matrix.of_apply, Fin.prod_univ_succ]`. Both sides reduce to the same expression. Rewrite using `[h, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, ih, ← pow_mul, ← pow_add]`. Use `congr 1`. Simplify using `only [Fintype.card_fun, Fintype.card_fin]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_kroneckerPower (R : Type) [CommRing R] (N r : ℕ) (B : Matrix (Fin N) (Fin N) R) :
    (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c)).det
      = B.det ^ ((r + 1) * N ^ r) := by
  induction r with
  | zero =>
    have h : (Matrix.of fun (I I' : Fin (0 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = B.submatrix (Equiv.funUnique (Fin 1) (Fin N)) (Equiv.funUnique (Fin 1) (Fin N)) := by
      ext I I'
      simp
    rw [h, Matrix.det_submatrix_equiv_self]
    simp
  | succ r ih =>
    have h : (Matrix.of fun (I I' : Fin (r + 1 + 1) → Fin N) => ∏ c, B (I c) (I' c))
        = (B ⊗ₖ (Matrix.of fun (I I' : Fin (r + 1) → Fin N) => ∏ c, B (I c) (I' c))).submatrix
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm
          (Fin.consEquiv (fun _ : Fin (r + 1 + 1) => Fin N)).symm := by
      ext I I'
      rw [Matrix.of_apply, Fin.prod_univ_succ]
      rfl
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, ih, ← pow_mul, ← pow_add]
    congr 1
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

end GlobalTheory
