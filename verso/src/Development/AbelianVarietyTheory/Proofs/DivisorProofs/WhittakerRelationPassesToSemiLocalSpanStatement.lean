import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWhittakerRelationPassesToSemiLocalSpan.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
