import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

/- English proof (translation)
Introduce `l hl c`. Take `⟨hc, hf, hlm, -, -, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Use `⟨hc, hf, ?_⟩` and prove the remaining obligations. Establish `h0 : (l : IsLocalRing.ResidueField c.O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]`.

Conclude with `hlm`. Conclude with `(CharP.charP_iff_prime_eq_zero hl.out).2 h0`.
-/
theorem UpperTheory.V.Pr.coefIs :
    UpperTheory.V.Pr.CoefIs := by
  intro l hl c
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, ?_⟩
  have h0 : (l : IsLocalRing.ResidueField c.O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  exact (CharP.charP_iff_prime_eq_zero hl.out).2 h0
