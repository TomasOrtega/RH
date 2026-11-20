import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsZonalSphericalFunctionUnramifiedUnitary
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsZonalSphericalFunctionUnramifiedUnitary.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | exact GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists.exists_isZonal <;> assumption)
