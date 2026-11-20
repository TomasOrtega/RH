import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QbBasisApply

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

/- English proof (translation)
Introduce `hA n _ M CF`. Use `⟨?_, fun R _ => qb_basisR hA CF R⟩` and prove the remaining obligations. Use `qb_basisR hA CF ℤ` as an intermediate fact. Rewrite `this` using `[qb_vecF_int]`. Conclude with `this`.
-/
theorem filtration_theorem_one_of : LemmaA → ColumnFamilyStandardVectorsBasis := by
  intro hA n _ M CF
  refine ⟨?_, fun R _ => qb_basisR hA CF R⟩
  have := qb_basisR hA CF ℤ
  rw [qb_vecF_int] at this
  exact this

end Formalism.InvariantFactorPaths.ColumnFamilies
