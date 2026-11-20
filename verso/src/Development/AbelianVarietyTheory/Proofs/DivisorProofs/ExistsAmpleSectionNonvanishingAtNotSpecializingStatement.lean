import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializing
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsAmpleSectionNonvanishingAtNotSpecializing.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x → ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | exact GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | (intros; apply GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes <;> assumption)
