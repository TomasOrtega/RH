import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LkMarks
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinEndOfFinPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrthogonalPairingFromIntertwiner
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

/- English proof (translation)
Establish `h2 : B.valuation (2 : Ω) < 1`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h4 : (1 : _) ≤ B.valuation (2 : Ω) * B.valuation (2 : Ω)` using `one_le_mul hc hc`. Rewrite `h4` using `[← map_mul]`.

Establish `: ((4 : ℕ) : Ω) = 2 * 2` using `by norm_num`. Rewrite `h` using `[this]`. Conclude with `absurd h (not_lt.mpr h4)`. Take `⟨k, rfl⟩` from `hM`. Establish `hk : B.valuation (k : Ω) ≤ 1`.

Use `B.valuation_le_one (k : B)` as an intermediate fact. Simplify using `using this`. Establish `: ((k + k : ℕ) : Ω) = 2 * (k : Ω)` using `by push_cast; ring`. Rewrite using `[this, map_mul]`. Conclude with `mul_lt_one_of_lt_of_le h2 hk`.
-/
private theorem val_of_even {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {M : ℕ} (hM : Even M)
    (h : B.valuation ((4 : ℕ) : Ω) < 1) : B.valuation (M : Ω) < 1 := by
  have h2 : B.valuation (2 : Ω) < 1 := by
    by_contra hc
    push_neg at hc
    have h4 : (1 : _) ≤ B.valuation (2 : Ω) * B.valuation (2 : Ω) := one_le_mul hc hc
    rw [← map_mul] at h4
    have : ((4 : ℕ) : Ω) = 2 * 2 := by norm_num
    rw [this] at h
    exact absurd h (not_lt.mpr h4)
  obtain ⟨k, rfl⟩ := hM
  have hk : B.valuation (k : Ω) ≤ 1 := by
    have := B.valuation_le_one (k : B)
    simpa using this
  have : ((k + k : ℕ) : Ω) = 2 * (k : Ω) := by push_cast; ring
  rw [this, map_mul]
  exact mul_lt_one_of_lt_of_le h2 hk
