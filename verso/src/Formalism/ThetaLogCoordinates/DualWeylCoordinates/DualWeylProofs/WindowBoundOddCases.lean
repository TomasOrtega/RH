import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem filtration_theorem_one_of : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  have := qb_basisR hA CF ℤ
  rw [qb_vecF_int] at this
  exact this

end Formalism.InvariantFactorPaths.ColumnFamilies
