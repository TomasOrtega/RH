import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignature
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FCardNegativeSignsDiagonalFrameEqSignature.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature : ∀ {D : D7} (V : HSp D), V.SigOK → ∀ (A : Fr V) (τ : D.what₂.Tau), (Finset.univ.filter fun a => A.ε τ a = false).card = (V.sig (tauE D τ)).2 := by
  first | exact @GlobalTheory.FrameSylvester.neg_card_eq_sig | exact GlobalTheory.FrameSylvester.neg_card_eq_sig | (intros; apply GlobalTheory.FrameSylvester.neg_card_eq_sig <;> assumption)
