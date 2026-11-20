import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateSplitPlaceAndUniformizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsConjugateSplitPlaceAndUniformizer.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) := by
  first | exact @GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | exact GlobalTheory.SplitExConj.exists_splitPlace_conj_unif | (intros; apply GlobalTheory.SplitExConj.exists_splitPlace_conj_unif <;> assumption)
