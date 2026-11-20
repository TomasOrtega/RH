import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernEvaluationCollapseVertical
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousCollapseQ
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernEvaluationCollapseVertical.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.chern_evaluation_collapse_vertical : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) [Fact p.Prime] (hp : p.Prime) (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ), evC (mdlOf z jc) (rootOf z jc) G - aeval (fun x => (mdlOf z jc).Z.c1 (rootOf z jc (false, x))) (GlobalTheory.ConsNumber.collapseQ D N G) ∈ Ideal.span (Set.range (mdlOf z jc).Z.cD) := by
  first | exact @GlobalTheory.ConsNumber.VertRoots.evC_sub_collapseQ_mem | exact GlobalTheory.ConsNumber.VertRoots.evC_sub_collapseQ_mem | (intros; apply GlobalTheory.ConsNumber.VertRoots.evC_sub_collapseQ_mem <;> assumption)
