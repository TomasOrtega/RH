import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRationalPointsSupportDefiniteUnitaryTestFu
open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

/- English proof (translation)
Introduce `E _ _ _ A w y`. Establish `hb : ((A.bar y : 𝓞 E) : E) = IsCMField.complexConj E (y : E)` using `A.bar_eq y`. Establish `hv` using `GlobalTheory.BCT.SuppFin.valuation_conj E w (y : E)`. Rewrite `hv` using `[← hb]`. Establish `h1` using `HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (A.bar y)`.

Establish `h2` using `HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (CertificateRingHomMap.cj w) y`. Rewrite using `[← h1, ← h2]`. Conclude with `iff_of_eq (congrArg (· < 1) hv.symm)`.
-/
theorem UpperTheory.Gal.G1.pCjMem :
    CjMem := by
  intro E _ _ _ A w y
  have hb : ((A.bar y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := A.bar_eq y
  have hv := GlobalTheory.BCT.SuppFin.valuation_conj E w (y : E)
  rw [← hb] at hv
  have h1 := HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (A.bar y)
  have h2 := HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (CertificateRingHomMap.cj w) y
  rw [← h1, ← h2]
  exact iff_of_eq (congrArg (· < 1) hv.symm)
