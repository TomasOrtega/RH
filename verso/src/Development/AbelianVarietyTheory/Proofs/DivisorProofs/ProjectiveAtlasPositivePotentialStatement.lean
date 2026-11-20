import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveAtlasPositivePotential
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BoundaryPolynomialFunctions
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FubiniStudyPot.exists_posPot` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FProjectiveAtlasPositivePotential.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.projective_atlas_positive_potential : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (B : FinHolAtlas n Y), IsProjective B → ∃ Om : LocPot Y, IsPotential B Om ∧ IsPosPot B Om := by
  first | exact @GlobalTheory.FubiniStudyPot.exists_posPot | exact GlobalTheory.FubiniStudyPot.exists_posPot | (intros; apply GlobalTheory.FubiniStudyPot.exists_posPot <;> assumption)
