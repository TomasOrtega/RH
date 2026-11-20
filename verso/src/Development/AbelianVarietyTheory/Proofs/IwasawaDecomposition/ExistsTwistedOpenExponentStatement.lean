import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistedOpenExponent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsTwistedOpenExponent.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_twisted_open_exponent : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D' : D7) (b : NBuilt hL D'), Elem b.D → GlobalTheory.RowTie.ChebSplit b.D.nd → ∃ Tw : TwOpen (withLoc b.L) (chL b.L b.C) (cfL b.L b.cf) (tpL b.L b.tp) (mtL b.L b.M) b.low, ExpRel b.L b.Bs.exp Tw.exp := by
  first | exact @GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel | exact GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel | (intros; apply GlobalTheory.HeightCounting.FitTwExp.exists_twOpen_expRel <;> assumption)
