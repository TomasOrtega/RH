import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHasModelOfSpreading.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.has_model_of_spreading : GlobalTheory.SpreadingModels.SchemeModels → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) → GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) → GlobalTheory.SpreadingModels.LBSpreads → ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f → ∀ M : LB Y, M.IsLB → GlobalTheory.SpreadingModels.HasModel f M := by
  first | exact @GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | exact GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads | (intros; apply GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads <;> assumption)
