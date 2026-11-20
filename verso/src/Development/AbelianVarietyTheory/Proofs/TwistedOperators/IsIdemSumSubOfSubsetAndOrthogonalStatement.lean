import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IdemSubDiff.isIdemSum_sdiff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsIdemSumSubOfSubsetAndOrthogonal.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  first | exact @GlobalTheory.IdemSubDiff.isIdemSum_sdiff | exact GlobalTheory.IdemSubDiff.isIdemSum_sdiff | (intros; apply GlobalTheory.IdemSubDiff.isIdemSum_sdiff <;> assumption)
