import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCuspFormEqZeroOfWhittakerVanishing.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  first | exact @GlobalTheory.JSW.eq_zero_of_whit_eq_zero | exact GlobalTheory.JSW.eq_zero_of_whit_eq_zero | (intros; apply GlobalTheory.JSW.eq_zero_of_whit_eq_zero <;> assumption)
