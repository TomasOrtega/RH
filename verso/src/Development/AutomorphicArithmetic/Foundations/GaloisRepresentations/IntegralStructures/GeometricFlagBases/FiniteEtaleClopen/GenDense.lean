import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Introduce a local definition for the expression.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem genDense : GenDense := by
  intro O _ _ Y p hp
  have hg : GeneralizingMap p := Flat.generalizingMap p
  rw [dense_iff_inter_open]
  rintro U hU ⟨y, hy⟩
  let η : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y', hy', hpy'⟩ := hg hη
  exact ⟨y', hy'.mem_open hU hy, by simp only [Set.mem_setOf_eq, hpy', η]⟩

end UpperTheory.Gal.Int.Geo.Cut
