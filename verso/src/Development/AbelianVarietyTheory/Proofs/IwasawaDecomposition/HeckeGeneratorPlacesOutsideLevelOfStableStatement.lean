import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeneratorPlacesOutsideLevelOfStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GenHypOut.genHyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckeGeneratorPlacesOutsideLevelOfStable.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  first | exact @GlobalTheory.GenHypOut.genHyp | exact GlobalTheory.GenHypOut.genHyp | (intros; apply GlobalTheory.GenHypOut.genHyp <;> assumption)
