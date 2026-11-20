import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFlagCharPrimitiveMovedLatticeLargeDepth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FJacobiFlagCharPrimitiveMovedLatticeLargeDepth.lean&line=88#L88)
-/
theorem _root_.GlobalTheory.T.jacobiFlagChar_primitive_movedLattice_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v := by
  first | exact @GlobalTheory.RowShape.big_primAt_rowJac | exact GlobalTheory.RowShape.big_primAt_rowJac | (intros; apply GlobalTheory.RowShape.big_primAt_rowJac <;> assumption)
