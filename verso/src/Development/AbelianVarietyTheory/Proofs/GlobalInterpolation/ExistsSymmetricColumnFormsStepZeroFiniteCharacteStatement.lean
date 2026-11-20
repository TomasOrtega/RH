import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacte
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsSymmetricColumnFormsStepZeroFiniteCharacte.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ C : ColsTiedSym (I.rec7 l Z), ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u) := by
  first | exact @GlobalTheory.Mem.Col2.TC.colsTiedSym_chiFin0 | exact GlobalTheory.Mem.Col2.TC.colsTiedSym_chiFin0 | (intros; apply GlobalTheory.Mem.Col2.TC.colsTiedSym_chiFin0 <;> assumption)
