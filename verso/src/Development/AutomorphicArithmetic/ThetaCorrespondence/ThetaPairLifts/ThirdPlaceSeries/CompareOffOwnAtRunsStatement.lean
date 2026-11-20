import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonOffTypePlacesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompareOffOwnAtRuns

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.compareOffOwn_atRuns_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FCompareOffOwnAtRuns.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.bigOn_comparison_at_twisted_places : (_root_.GlobalTheory.BigOn.ForallTwoRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) := by
  first | exact @_root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt | exact _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt | (intros; apply _root_.GlobalTheory.BigOn.compareOffOwn_atRuns_alt <;> assumption)
end
