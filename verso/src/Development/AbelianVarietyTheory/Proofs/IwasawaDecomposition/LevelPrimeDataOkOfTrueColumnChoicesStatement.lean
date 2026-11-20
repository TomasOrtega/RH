import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLevelPrimeDataOkOfTrueColumnChoices.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  first | exact @GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | exact GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | (intros; apply GlobalTheory.Mem.Col2.LevelLaw.atIn_ok <;> assumption)
