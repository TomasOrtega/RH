import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficients
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHilbertEisensteinJetAlgebraicQCoefficients.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ), QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | exact GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | (intros; apply GlobalTheory.HilbFam.qAll_isAlgebraic_hfun <;> assumption)
