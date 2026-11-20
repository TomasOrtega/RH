import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenMass.Fibre.termLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLocalTermLatticeOverInnerDatumFgSpan.lean&line=305#L305)
-/
theorem _root_.GlobalTheory.T.localTermLattice_over_innerDatum_fg_span : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D) (d : LocNG.Datum (FP p)) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS), LocNG.IsTermOver (FP p) d t → t.abelian₂.FG ∧ Submodule.span (D.s.atP p).Ep (t.abelian₂ : Set (Vp D p)) = ⊤ := by
  first | exact @GlobalTheory.GenMass.Fibre.termLat | exact GlobalTheory.GenMass.Fibre.termLat | (intros; apply GlobalTheory.GenMass.Fibre.termLat <;> assumption)
