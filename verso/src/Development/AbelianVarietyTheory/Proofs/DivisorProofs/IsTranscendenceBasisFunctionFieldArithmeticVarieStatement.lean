import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarie
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsTranscendenceBasisFunctionFieldArithmeticVarie.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∃ x : Fin D → X.functionField, IsTranscendenceBasis ℤ x) ∧ ∀ x : Fin D → X.functionField, AlgebraicIndependent ℤ x → IsTranscendenceBasis ℤ x := by
  first | exact @GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | exact GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField | (intros; apply GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField <;> assumption)
