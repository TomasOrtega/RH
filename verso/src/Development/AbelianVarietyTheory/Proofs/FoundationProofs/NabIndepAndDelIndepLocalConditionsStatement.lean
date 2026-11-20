import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NabIndepAndDelIndepLocalConditions
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TestLat.nabIndep_and_delIndep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FNabIndepAndDelIndepLocalConditions.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.nabIndep_and_delIndep_local_conditions : NabIndep ∧ DelIndep := by
  first | exact @GlobalTheory.TestLat.nabIndep_and_delIndep | exact GlobalTheory.TestLat.nabIndep_and_delIndep | (intros; apply GlobalTheory.TestLat.nabIndep_and_delIndep <;> assumption)
