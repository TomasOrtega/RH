import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCdvrReadingInCpOfFiniteResidue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GeoTie.ReadExist.exists_isReading` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsCdvrReadingInCpOfFiniteResidue.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_cdvrReadingInCp_of_finiteResidue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (e : ℕ), OverLa (placeAt φ) T.V io e → T.FinRes → ∃ k : T.Fr →+* ℂ_[p], IsReading φ T io k := by
  first | exact @GlobalTheory.GeoTie.ReadExist.exists_isReading | exact GlobalTheory.GeoTie.ReadExist.exists_isReading | (intros; apply GlobalTheory.GeoTie.ReadExist.exists_isReading <;> assumption)
