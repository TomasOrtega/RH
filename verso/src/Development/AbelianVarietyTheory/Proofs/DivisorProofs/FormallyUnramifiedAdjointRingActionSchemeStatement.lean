import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFormallyUnramifiedAdjointRingActionScheme.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.formallyUnramified_adjointRingAction_scheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_actRep | exact GlobalTheory.EndLoc.formallyUnramified_actRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_actRep; all_goals assumption)
