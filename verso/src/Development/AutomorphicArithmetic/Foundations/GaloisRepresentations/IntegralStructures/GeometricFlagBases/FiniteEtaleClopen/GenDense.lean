import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Introduce `O _ _ Y p hp`. Establish `hg : GeneralizingMap p` using `Flat.generalizingMap p`. Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `U hU ⟨y, hy⟩`. Set `η : PrimeSpectrum O` to `⟨⊥, Ideal.isPrime_bot⟩`.

Establish `hη : η ⤳ p y` using `(PrimeSpectrum.le_iff_specializes _ _).mp bot_le`. Take `⟨y', hy', hpy'⟩` from `hg hη`. Conclude with `⟨y', hy'.mem_open hU hy, by simp only [Set.mem_setOf_eq, hpy', η]⟩`.
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
