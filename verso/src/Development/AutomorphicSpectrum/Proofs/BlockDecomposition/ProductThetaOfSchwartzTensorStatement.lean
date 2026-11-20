import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FProductThetaOfSchwartzTensor.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | exact GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor <;> assumption)
