import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexLatticeEqAtMulSplitSupported
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MovedSplitEq.eqAt_latAt_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FVertexLatticeEqAtMulSplitSupported.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.vertexLattice_eqAt_mul_splitSupported : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ (q : ℕ), q.Prime → ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e →
    GlobalTheory.MovedKappaEx.OffPrime e q → ∀ g y : FinPt G X, SuppAt e (G.V X) g.1 →
    EqAt D q (GlobalTheory.SumSize.latAt S X (g * y)) (GlobalTheory.SumSize.latAt S X y) := by
  first | exact @GlobalTheory.MovedSplitEq.eqAt_latAt_mul | exact GlobalTheory.MovedSplitEq.eqAt_latAt_mul | (intros; apply GlobalTheory.MovedSplitEq.eqAt_latAt_mul <;> assumption)
