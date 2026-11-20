import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankAtPlacesFromComparison
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRankAtPlacesFromComparison.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.rank_at_places_from_comparison : MaxSt → GeoSt → (AtRuns fun Fm x _ i p r h => ∀ v ∈ p.R.twPl, ∀ j, letI : Algebra (r.used v).full.J.Q.c.F (Fm.D x i).what₂.LL := p.alg; GlobalTheory.TraceClassRank.CompareOffOwn (T := (r.used v).full) (R := R2 p) (h.laws v).p (fw2 p) j (r.lev j) (F2 p).P0 (F2 p).ψ0⁻¹ 1 v (ownAt (Fm.D x i) v)) → (AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) := by
  first | exact @GlobalTheory.BigOn.rankLocSt_of | exact GlobalTheory.BigOn.rankLocSt_of | (intros; apply GlobalTheory.BigOn.rankLocSt_of <;> assumption)
