import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinitePlaceStandardCharLocallyConstantNontrivial.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ, (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | exact GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | (intros; apply GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one <;> assumption)
