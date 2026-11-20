import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDifferentEqLocalGenerator
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocDiffGen.span_different_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSpanDifferentEqLocalGenerator.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.span_different_eq_localGenerator : ∀ (D : D7) (Z : LocDat D) (p : PlF D), Submodule.span (Z.M p).L.O ((fun x : 𝓞 D.host.F => (D.s.atP p).ιE (algebraMap D.host.F D.host.E x)) '' (differentIdeal ℤ (𝓞 D.host.F) : Set (𝓞 D.host.F))) = Submodule.span (Z.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p)} := by
  first | exact @GlobalTheory.LocDiffGen.span_different_eq | exact GlobalTheory.LocDiffGen.span_different_eq | (intros; apply GlobalTheory.LocDiffGen.span_different_eq <;> assumption)
