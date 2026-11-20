import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSignConeWeightIndicator.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.sign_cone_weight_indicator : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) a, PosFam y → gam y a = Set.indicator {a | ∀ e, sdot e a ≤ y e} 1 a := by
  first | exact @GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | exact GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | (intros; apply GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator <;> assumption)
