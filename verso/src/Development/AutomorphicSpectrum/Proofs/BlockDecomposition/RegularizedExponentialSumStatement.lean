import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
open scoped Classical
namespace PositivityTheory.Rg.BcB.F
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRegularizedExponentialSum.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.regularized_exponential_sum : PositivityTheory.Rg.BcB.F.ExpSum := by
  first | exact @GlobalTheory.CompanionTheory.ExpSums.expSum_holds | exact GlobalTheory.CompanionTheory.ExpSums.expSum_holds | (intros; apply GlobalTheory.CompanionTheory.ExpSums.expSum_holds <;> assumption)
