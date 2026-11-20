import Formalism.GradedWeylDivisibility.StatementD

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on`. Name the introduced variables `a`. Simplify using `[rowAct]`. Name the introduced variables `p q hp hq`. Simplify using `only [map_add, hp, hq]`.

Name the introduced variables `p v hp`. Simplify using `only [map_mul, hp]`. Use `congr 1`. Simplify using `[rowAct, Matrix.map_apply]`.
-/
theorem ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by
  induction F using MvPolynomial.induction_on
  · rename_i a
    simp [rowAct]
  · rename_i p q hp hq
    simp only [map_add, hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.map_apply]

end Formalism.GradedWeylDivisibility
