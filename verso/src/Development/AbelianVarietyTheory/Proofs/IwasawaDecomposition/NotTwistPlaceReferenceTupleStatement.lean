import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNotTwistPlaceReferenceTuple.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  first | exact @GlobalTheory.Mem.Col2.TC.not_underQ_mu0 | exact GlobalTheory.Mem.Col2.TC.not_underQ_mu0 | (intros; apply GlobalTheory.Mem.Col2.TC.not_underQ_mu0 <;> assumption)
