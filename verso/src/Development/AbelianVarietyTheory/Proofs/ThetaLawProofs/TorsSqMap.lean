import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem torsSq_map : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (R' : Type) [CommRing R'] (f : R →+* R') (t : R), TorsSq deg D t → TorsSq deg (D.map f) (f t) := by
  intro R Ix _ _ _ deg D R' _ f t H
  obtain ⟨h, h1, h2, e, h3⟩ := H
  refine ⟨h.map f, ?_, ?_, e, ?_⟩
  · intro p q hpq
    simp [Matrix.map_apply, h1 p q hpq]
  · have := congrArg (f.mapMatrix : Matrix Ix Ix R →+* Matrix Ix Ix R') h2
    rw [map_add, map_mul, map_mul, map_one] at this
    exact this
  · rw [h3, map_pow, RingHom.map_det]
    congr 2
    ext p q
    simp [Matrix.map_apply]

end GlobalTheory.KeyKa
