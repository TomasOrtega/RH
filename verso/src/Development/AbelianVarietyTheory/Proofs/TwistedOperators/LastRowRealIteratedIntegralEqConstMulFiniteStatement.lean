import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFinite
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RowRealInt.unfold_of_steps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLastRowRealIteratedIntegralEqConstMulFinite.lean&line=274#L274)
-/
theorem _root_.GlobalTheory.T.lastRow_real_iterated_integral_eq_const_mul_finite : CellVan → Big fun ch => GrpAt ch → IterAt ch → LinAt ch → InvAt ch → (∃ s, SuppOn ch s ∧ RepAt ch s ∧ ValAt ch s) → RealLine ch → (∀ t a, ch.S.SumOK t (ch.Phi a)) → UnfoldAt ch := by
  first | exact @GlobalTheory.RowRealInt.unfold_of_steps | exact GlobalTheory.RowRealInt.unfold_of_steps | (intros; apply GlobalTheory.RowRealInt.unfold_of_steps <;> assumption)
