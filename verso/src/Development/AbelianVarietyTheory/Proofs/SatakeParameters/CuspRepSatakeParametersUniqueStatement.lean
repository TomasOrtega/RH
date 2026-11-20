import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUnique
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AboveL.cg_hasSat_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCuspRepSatakeParametersUnique.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.cuspRep_satakeParameters_unique : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : ℕ) (π : CG K a) (w : HeightOneSpectrum (𝓞 K)) (B B' : Multiset ℂˣ), π.HasSat w B → π.HasSat w B' → B = B' := by
  first | exact @GlobalTheory.AboveL.cg_hasSat_unique | exact GlobalTheory.AboveL.cg_hasSat_unique | (intros; apply GlobalTheory.AboveL.cg_hasSat_unique <;> assumption)
